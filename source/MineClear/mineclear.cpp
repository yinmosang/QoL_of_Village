// mineclear.cpp —— 独立 MOD：矿洞矿石掉落倍增（MineClear v1.0.0）
//
// 从 ProductionAuto 的 PaMyBoostTick 拆出，改为自包含单文件工程。
// 设计原则（第十六轮实机验证结论）：
//   * 绝不构造任何物品对象，只把「游戏自己掉进背包」的增量按倍率补
//     stackCount —— 因此不可能凭空冒出错误物品。
//   * 只放大白名单 4 种：铁矿 240020 / 金矿 240030 / 陨铁矿 240040
//     / 煤矿 230100（煤矿单独 x5）。其余全部零写入。
//   * 静态名称表 production_hud_v2.inl 把 2400xx 段整体错标成「XX种子」，
//     本 MOD 完全不依赖它，只认运行时 itemId。
//   * 只在矿洞内（floor>0）生效；农作物 / 日常整理不受影响。
//   * 跨箱回收不在此 MOD 内重写：复用已实机验证、修过 F7 卡顿的
//     ChestSort_v1.4.8 DLL，由 ModManager 单独登记开关。
//
// 配置文件（游戏根目录）：qol_mineclear.txt
//   enabled=1 mul=3 ids=240020,240030,240040,230100@5 hotkey=F8
// 热键 F8 切换 enabled（边沿触发 + 写回配置文件 + 5 秒浮层提示）。

#include <windows.h>
#include <cstdint>
#include <cstring>
#include <cstdio>
#include <cwchar>

#include "logging.h"
#include "exe_guard.h"
#include "obs.h"
#include "quickmenu.h"

using u64 = unsigned long long;

// ============================================================
// 常量：build 25640656 / v1.30，全部来自 ProductionAuto + ChestSort
// 已实机验证的 RVA 与存档偏移
// ============================================================
static constexpr uintptr_t kRvaGameRoot        = 0x111cc90;
static constexpr uintptr_t kRvaItemAdjust      = 0x10B920;
static constexpr uintptr_t kRvaCommandCapacity = 0x4FF1B0;
static constexpr uintptr_t kRvaBatchRecalc     = 0x149BF0;
static constexpr uintptr_t kRvaBatchUiRefresh  = 0xFD4F0;
static constexpr uintptr_t kRvaBatchDirty      = 0x147980;

static constexpr uintptr_t kOffSave        = 0x208;   // root -> save(player)
static constexpr uintptr_t kOffLevel      = 0x34E8;  // save -> level object
static constexpr uintptr_t kOffFloor      = 0x34;
static constexpr uintptr_t kOffRem        = 0x3C;
static constexpr uintptr_t kOffBag        = 0x32C0;  // save -> bag slots[30]
static constexpr uintptr_t kOffItemRefs   = 0x008;
static constexpr uintptr_t kOffItemHolder = 0x240;
static constexpr uintptr_t kOffItemCount  = 0x260;

// ============================================================
// 原生函数签名（与 ProductionAuto/nearby_chest_sort.inl 一致）
// ============================================================
struct CommandItem {
    void* item;
    unsigned char tail[0x10];
};
static_assert(sizeof(CommandItem) == 0x18,
              "native CommandItem layout changed");

using FnItemAdjust      = void (__fastcall *)(void*, int);
using FnCommandCapacity = int  (__fastcall *)(CommandItem*);
using FnBatchRecalc     = void (__fastcall *)(void*, bool);
using FnBatchUiRefresh  = void (__fastcall *)(void*, bool);
using FnBatchDirty      = void (__fastcall *)(void*, int);

static FnItemAdjust      g_adjust     = nullptr;
static FnCommandCapacity g_capacity   = nullptr;
static FnBatchRecalc     g_recalc     = nullptr;
static FnBatchUiRefresh  g_uiRefresh  = nullptr;
static FnBatchDirty      g_dirty      = nullptr;

static volatile long g_ready    = 0;
static volatile long g_enabled  = 1;
static volatile long g_mul      = 3;
static volatile long g_idCount  = 0;
static volatile WORD g_hotkeyVk = VK_F8;
// 两个可热调旋钮：scanms= 放大扫描间隔（默认 250ms），
// refresh= 是否调用原生三件套刷新（默认 1）。用于零编译定位性能问题。
static volatile long g_scanMs   = 250;
static volatile long g_refresh  = 1;
static u64  g_ids[16]   = {};
static long g_idMul[16] = {};

// ============================================================
// 基础读取工具（已提交区域缓存版）
//
// 【掉帧根因 / 2026-11-15 第十八轮】
// ProductionAuto 的 NearbyIsReadable 带 256 项区域缓存，绝大多数检查
// 只是一次整数比较。拆分版早期这里每次都直接调 VirtualQuery：
//   30 个背包槽 x 每槽 5 次可读性检查 = 150 次 / 次扫描
//   旧 DLL 每 100ms 扫一次 => 1500 次 VirtualQuery / 秒
// 该游戏进程堆区域多、VAD 树大，VirtualQuery 极慢（历史上 F7 遍历
// 2502 个节点耗时 3.4~3.8 秒就是同一个 API），足以把主线程吃满。
// 这就解释了「开倍增就卡爆、关掉就正常 / 矿洞内巨卡」。
//
// 现在：缓存命中只做两次整数比较，未命中才 VirtualQuery 一次并登记
// 整段已提交区域（物品对象通常集中在 1~3 个堆区域里）。
// ============================================================
struct ReadRegion {
    uintptr_t begin;
    uintptr_t end;
};
static ReadRegion g_regions[64] = {};
static long       g_regionCount = 0;
static ULONGLONG  g_regionEpoch = 0;
static long       g_vqCount     = 0;   // 真实 VirtualQuery 次数（PERF 诊断）
static long       g_cacheHits   = 0;   // 缓存命中次数（PERF 诊断）
static long       g_scanCount   = 0;   // 背包逐槽扫描次数（PERF 诊断）

// 每 30 秒重建缓存，避免页面被释放后仍按陈旧区域放行。
// 只在每次 tick 开头调一次，热路径里不出现任何系统调用。
static void RegionTick() {
    const ULONGLONG now = GetTickCount64();
    if (now - g_regionEpoch > 30000ULL) {
        g_regionEpoch = now;
        g_regionCount = 0;
    }
}

static void* Rva(uintptr_t rva) {
    return reinterpret_cast<void*>(
        reinterpret_cast<uintptr_t>(GetModuleHandleW(nullptr)) + rva);
}

static bool Readable(const void* p, size_t n) {
    if (!p || n == 0) return false;
    const uintptr_t start = reinterpret_cast<uintptr_t>(p);
    if (start < 0x10000) return false;
    const uintptr_t end = start + n;
    if (end < start) return false;

    for (long i = 0; i < g_regionCount; ++i) {
        if (start >= g_regions[i].begin && end <= g_regions[i].end) {
            ++g_cacheHits;
            return true;
        }
    }

    ++g_vqCount;
    MEMORY_BASIC_INFORMATION mbi = {};
    if (!VirtualQuery(p, &mbi, sizeof(mbi))) return false;
    if (mbi.State != MEM_COMMIT) return false;
    if (mbi.Protect & (PAGE_GUARD | PAGE_NOACCESS)) return false;
    const uintptr_t regionBegin =
        reinterpret_cast<uintptr_t>(mbi.BaseAddress);
    const uintptr_t regionEnd = regionBegin + mbi.RegionSize;
    if (end > regionEnd) return false;
    if (g_regionCount < 64) {
        g_regions[g_regionCount].begin = regionBegin;
        g_regions[g_regionCount].end = regionEnd;
        ++g_regionCount;
    }
    return true;
}

static bool ReadPtr(const void* base, uintptr_t off, void** out) {
    void* const* slot = reinterpret_cast<void* const*>(
        reinterpret_cast<uintptr_t>(base) + off);
    if (!Readable(slot, sizeof(void*))) return false;
    *out = *slot;
    return *out != nullptr;
}

struct ItemInfo { u64 id; int count; };

static bool ReadItem(void* item, ItemInfo* out) {
    if (!item || !out) return false;
    unsigned char* b = reinterpret_cast<unsigned char*>(item);
    if (!Readable(b + kOffItemRefs, sizeof(LONG))) return false;
    if (*reinterpret_cast<const LONG*>(b + kOffItemRefs) <= 0) return false;
    if (!Readable(b + kOffItemHolder, sizeof(void*)) ||
        !Readable(b + kOffItemCount, sizeof(int))) return false;
    void* holder = *reinterpret_cast<void* const*>(b + kOffItemHolder);
    void* data = nullptr;
    if (!ReadPtr(holder, 0, &data) || !Readable(data, sizeof(u64))) return false;
    out->id = *reinterpret_cast<const u64*>(data);
    out->count = *reinterpret_cast<const int*>(b + kOffItemCount);
    return out->id != 0 && out->count > 0 && out->count <= 999;
}

static void* GetSave() {
    void* root = nullptr;
    void* save = nullptr;
    if (!ReadPtr(Rva(kRvaGameRoot), 0, &root)) return nullptr;
    if (!ReadPtr(root, kOffSave, &save)) return nullptr;
    return save;
}

static bool ReadLevel(void* save, unsigned int* floor, unsigned int* rem) {
    void* lvl = nullptr;
    if (!ReadPtr(save, kOffLevel, &lvl)) return false;
    unsigned char* b = reinterpret_cast<unsigned char*>(lvl);
    if (!Readable(b + kOffFloor, 0x10)) return false;
    *floor = *reinterpret_cast<const unsigned int*>(b + kOffFloor);
    *rem   = *reinterpret_cast<const unsigned int*>(b + kOffRem);
    return true;
}

// ============================================================
// SEH 安全调用（noinline，杜绝 C2712）
// ============================================================
__declspec(noinline) static void SafeAdjust(void* item, int delta) {
    if (!g_adjust) return;
    __try { g_adjust(item, delta); }
    __except (EXCEPTION_EXECUTE_HANDLER) {}
}

__declspec(noinline) static int SafeCapacity(CommandItem* d) {
    int r = 0;
    if (!g_capacity) return 0;
    __try { r = g_capacity(d); }
    __except (EXCEPTION_EXECUTE_HANDLER) { r = 0; }
    return r;
}

__declspec(noinline) static void SafeRefresh(void* player) {
    __try { if (g_recalc) g_recalc(player, false); }
    __except (EXCEPTION_EXECUTE_HANDLER) {}
    __try { if (g_uiRefresh) g_uiRefresh(player, true); }
    __except (EXCEPTION_EXECUTE_HANDLER) {}
    __try { if (g_dirty) g_dirty(player, 0x2bc); }
    __except (EXCEPTION_EXECUTE_HANDLER) {}
}

__declspec(noinline) static void Toast(long on, long mul) {
    qol::obs::EventF(1, qol::obs::OBS_TOAST_MS,
        L"[矿洞倍增] %s（铁矿/金矿/陨铁矿 x%ld，煤矿 x5）",
        on ? L"已开启" : L"已关闭", mul);
}

// ============================================================
// 配置（游戏根目录 qol_mineclear.txt，500ms 热轮询）
// ============================================================
static void ConfigPath(wchar_t* path, size_t cap) {
    wchar_t dir[MAX_PATH] = {};
    if (!GetModuleFileNameW(nullptr, dir, MAX_PATH)) {
        path[0] = 0;
        return;
    }
    wchar_t* slash = wcsrchr(dir, L'\\');
    if (!slash) { path[0] = 0; return; }
    *(slash + 1) = 0;
    wcscpy_s(path, cap, dir);
    wcscat_s(path, cap, L"qol_mineclear.txt");
}

static const char* Find(const char* s, const char* key) {
    if (!s || !key) return nullptr;
    for (const char* p = s; *p; ++p) {
        const char* a = p;
        const char* b = key;
        while (*a && *b && *a == *b) { ++a; ++b; }
        if (!*b) return p;
    }
    return nullptr;
}

static u64 ParseU64(const char* p) {
    u64 v = 0;
    if (!p) return 0;
    while (*p == ' ' || *p == '\t') ++p;
    while (*p >= '0' && *p <= '9') {
        v = v * 10ULL + static_cast<unsigned>(*p - '0');
        ++p;
    }
    return v;
}

static WORD ParseVk(const char* s) {
    while (*s == ' ' || *s == '\t' || *s == '\r' || *s == '\n') ++s;
    if ((s[0] == 'F' || s[0] == 'f') && s[1] >= '0' && s[1] <= '9') {
        int n = s[1] - '0';
        if (n == 1 && s[2] >= '0' && s[2] <= '2') n = 10 + (s[2] - '0');
        if (n >= 1 && n <= 12) return static_cast<WORD>(VK_F1 + n - 1);
    }
    if (s[0] >= '0' && s[0] <= '9') return static_cast<WORD>(s[0]);
    if (s[0] >= 'A' && s[0] <= 'Z') return static_cast<WORD>(s[0]);
    if (s[0] >= 'a' && s[0] <= 'z')
        return static_cast<WORD>(s[0] - 'a' + 'A');
    return VK_F8;
}

static void PollConfig() {
    static ULONGLONG s_last = 0;
    const ULONGLONG now = GetTickCount64();
    if (now - s_last < 500ULL) return;
    s_last = now;

    wchar_t path[MAX_PATH] = {};
    ConfigPath(path, MAX_PATH);
    if (!path[0]) return;

    char buf[256] = {};
    HANDLE h = CreateFileW(path, GENERIC_READ,
                           FILE_SHARE_READ | FILE_SHARE_WRITE, nullptr,
                           OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, nullptr);
    if (h == INVALID_HANDLE_VALUE) return;   // 文件不存在：沿用内置默认值
    DWORD got = 0;
    ReadFile(h, buf, sizeof(buf) - 1, &got, nullptr);
    CloseHandle(h);
    if (got >= sizeof(buf)) got = sizeof(buf) - 1;
    buf[got] = 0;

    const char* p = Find(buf, "enabled=");
    if (p) InterlockedExchange(&g_enabled, ParseU64(p + 8) ? 1 : 0);
    p = Find(buf, "mul=");
    if (p) {
        long m = static_cast<long>(ParseU64(p + 4));
        if (m < 2) m = 2;
        if (m > 20) m = 20;
        InterlockedExchange(&g_mul, m);
    }
    p = Find(buf, "hotkey=");
    if (p) g_hotkeyVk = ParseVk(p + 7);

    p = Find(buf, "scanms=");
    if (p) {
        long ms = static_cast<long>(ParseU64(p + 7));
        if (ms < 100) ms = 100;
        if (ms > 2000) ms = 2000;
        InterlockedExchange(&g_scanMs, ms);
    }
    p = Find(buf, "refresh=");
    if (p) InterlockedExchange(&g_refresh, ParseU64(p + 8) ? 1 : 0);

    // ids= 支持 id 或 id@倍率；不写则沿用内置 4 种
    p = Find(buf, "ids=");
    if (p) {
        p += 4;
        long n = 0;
        while (*p && n < 16) {
            while (*p == ' ' || *p == ',' || *p == '\t') ++p;
            if (*p < '0' || *p > '9') break;
            u64 v = 0;
            while (*p >= '0' && *p <= '9') {
                v = v * 10ULL + static_cast<unsigned>(*p - '0');
                ++p;
            }
            long per = 0;
            if (*p == '@') {
                ++p;
                while (*p >= '0' && *p <= '9') {
                    per = per * 10 + (*p - '0');
                    ++p;
                }
            }
            g_ids[n] = v;
            g_idMul[n] = per;
            ++n;
        }
        InterlockedExchange(&g_idCount, n);
    }
}

// F8 边沿触发：切换开关、写回配置文件、弹 5 秒浮层
static void WriteEnabled(long on) {
    wchar_t path[MAX_PATH] = {};
    ConfigPath(path, MAX_PATH);
    if (!path[0]) return;
    char buf[256] = {};
    HANDLE h = CreateFileW(path, GENERIC_READ,
                           FILE_SHARE_READ | FILE_SHARE_WRITE, nullptr,
                           OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, nullptr);
    if (h == INVALID_HANDLE_VALUE) return;
    DWORD got = 0;
    ReadFile(h, buf, sizeof(buf) - 1, &got, nullptr);
    CloseHandle(h);
    if (got >= sizeof(buf)) got = sizeof(buf) - 1;
    buf[got] = 0;
    char* e = const_cast<char*>(Find(buf, "enabled="));
    if (e && e[8] >= '0' && e[8] <= '9') {
        e[8] = on ? '1' : '0';
    } else if (got + 12 < sizeof(buf)) {
        e = buf + got;
        memcpy(e, "enabled=1\r\n", 11);
        if (on == 0) e[8] = '0';
        got += 11;
        buf[got] = 0;
    }
    HANDLE w = CreateFileW(path, GENERIC_WRITE, FILE_SHARE_READ, nullptr,
                           CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, nullptr);
    if (w == INVALID_HANDLE_VALUE) return;
    DWORD written = 0;
    WriteFile(w, buf, got, &written, nullptr);
    CloseHandle(w);
}

static void PollHotkey() {
    static bool s_needsRelease = true;
    const bool down = (GetAsyncKeyState(g_hotkeyVk) & 0x8000) != 0;
    bool pressed = false;
    if (s_needsRelease) {
        if (!down) s_needsRelease = false;
    } else if (down) {
        pressed = true;
        s_needsRelease = true;
    }
    if (!pressed) return;
    const long on = InterlockedCompareExchange(&g_enabled, 0, 0);
    const long next = on ? 0 : 1;
    InterlockedExchange(&g_enabled, next);
    WriteEnabled(next);
    Toast(next, static_cast<long>(g_mul));
    Log("[MineClear] hotkey toggle -> enabled=%ld\n", next);
}

// ============================================================
// 核心：只放大游戏原生掉进背包的白名单物品
// ============================================================
static void BoostTick() {
    RegionTick();
    void* save = GetSave();
    if (!save) return;
    unsigned int floor = 0;
    unsigned int rem = 0;
    if (!ReadLevel(save, &floor, &rem)) return;
    if (floor == 0 || floor > 200 || rem >= 0xFFFF0000u) return;

    // 【性能 / 第十八轮】绝不无条件扫背包。
    // level 对象是常驻的，矿洞外 floor 也可能读到非 0；旧版只要 floor>0
    // 就每 100ms 扫一次 30 槽，于是「矿洞外小卡、进矿洞巨卡」。
    // 现在只认「rem 下降」= 真正敲掉了石头才开一个 20 秒窗口：
    // 首次读到 / 换层只建基线不开窗；户外 rem 恒定 -> 永不扫描。
    static u64 s_ids[30] = {};
    static int s_counts[30] = {};
    static bool s_has = false;
    static unsigned int s_floor = 0;
    static unsigned int s_lastRem = 0xFFFFFFFFu;
    static ULONGLONG s_hitAt = 0;
    static ULONGLONG s_lastRefresh = 0;
    const ULONGLONG nowMs = GetTickCount64();

    if (floor != s_floor) {   // 换层：重建背包基线 + rem 基线，本拍不扫描
        s_floor = floor;
        s_has = false;
        s_lastRem = rem;
        s_hitAt = 0;
        return;
    }
    if (s_lastRem == 0xFFFFFFFFu) {   // 首次读到：只建基线
        s_lastRem = rem;
        return;
    }
    if (rem < s_lastRem) {            // 敲掉了石头 -> 开窗
        s_lastRem = rem;
        s_hitAt = nowMs;
    } else if (rem > s_lastRem) {     // rem 回升（换层等）：重建两条基线
        s_lastRem = rem;
        s_hitAt = 0;
        s_has = false;
        return;
    }
    if (s_hitAt == 0 || nowMs - s_hitAt > 20000ULL) return;

    void** slots = reinterpret_cast<void**>(
        reinterpret_cast<unsigned char*>(save) + kOffBag);
    if (!Readable(slots, 30 * sizeof(void*))) return;
    ++g_scanCount;

    u64 ids[30] = {};
    int counts[30] = {};
    void* items[30] = {};
    for (int i = 0; i < 30; ++i) {
        void* item = slots[i];
        if (!item) continue;
        ItemInfo info = {};
        if (!ReadItem(item, &info)) continue;
        ids[i] = info.id;
        counts[i] = info.count;
        items[i] = item;
    }
    if (!s_has) {
        memcpy(s_ids, ids, sizeof(ids));
        memcpy(s_counts, counts, sizeof(counts));
        s_has = true;
        return;
    }

    const long idCount = static_cast<long>(g_idCount);
    const long globalMul = static_cast<long>(g_mul);
    int boosted = 0;
    for (int i = 0; i < 30; ++i) {
        if (!ids[i] || !items[i]) continue;
        const bool same = (s_ids[i] == ids[i]);
        const int delta = same ? (counts[i] - s_counts[i]) : counts[i];
        if (delta <= 0) continue;

        long mul = 0;
        for (long k = 0; k < idCount; ++k) {
            if (g_ids[k] == ids[i]) {
                mul = g_idMul[k] > 0 ? g_idMul[k] : globalMul;
                break;
            }
        }
        // 非白名单零写入；不再逐条打 PASS 日志（诊断日志开着时会刷屏）
        if (mul <= 0) continue;
        if (mul > 20) mul = 20;

        ItemInfo before = {};
        if (!ReadItem(items[i], &before) || before.id != ids[i]) continue;
        int room = 999 - before.count;
        if (g_capacity) {
            CommandItem d = {};
            d.item = items[i];
            const int r = SafeCapacity(&d);
            if (r > 0 && r < room) room = r;
        }
        int extra = delta * (static_cast<int>(mul) - 1);
        if (extra > room) extra = room;
        if (extra > 999) extra = 999;
        if (extra <= 0) continue;

        SafeAdjust(items[i], extra);
        ItemInfo after = {};
        const bool ok = ReadItem(items[i], &after) &&
                        after.id == ids[i] &&
                        after.count == before.count + extra;
        if (ok) {
            Log("[MineClear] BOOST id=%llu %d->%d (drop +%d x%ld) "
                "layer=%u rem=%u\n",
                ids[i], before.count, after.count, delta, mul, floor, rem);
            ++boosted;
        } else {
            Log("[MineClear] VERIFY FAILED id=%llu before=%d after=%d "
                "want=%d\n", ids[i], before.count, after.count, extra);
        }
        // 快照对齐实际值，杜绝自激重复放大
        counts[i] = ok ? after.count : before.count;
    }

    memcpy(s_ids, ids, sizeof(ids));
    memcpy(s_counts, counts, sizeof(counts));
    // 三件套重算降频：窗口内最多每秒一次；refresh=0 可零编译整体关闭，
    // 便于隔离「到底是背包扫描还是原生刷新」造成的卡顿。
    if (boosted > 0 && g_refresh &&
        nowMs - s_lastRefresh > 1000ULL) {
        s_lastRefresh = nowMs;
        SafeRefresh(save);
    }
}

// 每 5 秒一行诊断：编译后可把 qol_log.cfg 临时设 level=1，
// 用 vq（真实 VirtualQuery 次数）确认缓存是否生效。level=0 时
// Log() 第一行就 return，这里只剩几个整数自增，无开销。
static void PerfLog() {
    static ULONGLONG s_last = 0;
    const ULONGLONG now = GetTickCount64();
    if (now - s_last < 5000ULL) return;
    s_last = now;
    Log("[MineClear] PERF scans=%ld vq=%ld cacheHits=%ld regions=%ld\n",
        g_scanCount, g_vqCount, g_cacheHits, g_regionCount);
    g_scanCount = 0;
    g_vqCount = 0;
    g_cacheHits = 0;
}

// ============================================================
// 入口
// ============================================================
static void BindNatives() {
    g_adjust    = reinterpret_cast<FnItemAdjust>(Rva(kRvaItemAdjust));
    g_capacity  = reinterpret_cast<FnCommandCapacity>(Rva(kRvaCommandCapacity));
    g_recalc    = reinterpret_cast<FnBatchRecalc>(Rva(kRvaBatchRecalc));
    g_uiRefresh = reinterpret_cast<FnBatchUiRefresh>(Rva(kRvaBatchUiRefresh));
    g_dirty     = reinterpret_cast<FnBatchDirty>(Rva(kRvaBatchDirty));
}

static bool QmIsOn() {
    return InterlockedCompareExchange(&g_enabled, 0, 0) != 0;
}
static void QmToggle() {
    const long next = QmIsOn() ? 0 : 1;
    InterlockedExchange(&g_enabled, next);
    WriteEnabled(next);
    Toast(next, static_cast<long>(g_mul));
}

extern "C" __declspec(dllexport) int QolQuickMenuItems(
        QolQuickMenuItem* items, int maxItems) {
    if (!items || maxItems < 1) return 0;
    items[0].name = "矿洞矿石倍增";
    items[0].isOn = QmIsOn;
    items[0].toggle = QmToggle;
    return 1;
}

extern "C" __declspec(dllexport) void mod_init(void) {
    LogOpen("mineclear");
    if (!qol::ExeBuildSupported()) {
        Log("[MineClear] game build mismatch -> disabled\n");
        return;
    }
    qol::obs::Init(nullptr);
    BindNatives();

    // 内置默认（配置文件不存在时也能直接用）
    g_ids[0] = 240020ULL; g_idMul[0] = 0;
    g_ids[1] = 240030ULL; g_idMul[1] = 0;
    g_ids[2] = 240040ULL; g_idMul[2] = 0;
    g_ids[3] = 230100ULL; g_idMul[3] = 5;
    InterlockedExchange(&g_idCount, 4);

    QolRegisterHotKey("mineclear", "F8");
    InterlockedExchange(&g_ready, 1);
    Log("[MineClear] mod_init OK (iron/gold/meteor x3, coal x5; F8 toggle)\n");
}

extern "C" __declspec(dllexport) void mod_tick(void) {
    // 兜底：少数加载器只分发 mod_tick 不调 mod_init，这里补一次且只补一次。
    if (!g_ready) {
        static volatile long s_initTried = 0;
        if (InterlockedCompareExchange(&s_initTried, 1, 0) == 0) mod_init();
        return;
    }
    PollHotkey();
    PollConfig();
    PerfLog();
    if (!g_enabled) return;
    static ULONGLONG s_last = 0;
    const ULONGLONG now = GetTickCount64();
    const ULONGLONG interval = static_cast<ULONGLONG>(g_scanMs);
    if (now - s_last < interval) return;   // 默认 250ms，可用 scanms= 热调
    s_last = now;
    BoostTick();
}

extern "C" __declspec(dllexport) void unload(void) {
    InterlockedExchange(&g_ready, 0);
    LogClose();
}

BOOL APIENTRY DllMain(HMODULE hModule, DWORD reason, LPVOID) {
    if (reason == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(hModule);
    }
    // 不调用 obs::Shutdown()：共享内存由其它 DLL 共用，单方关闭会互相影响
    return TRUE;
}
