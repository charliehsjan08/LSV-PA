// ==================== PA2: KL Cut Flexibility (lsv_kl_flex <k> <l>) ====================
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/bsat/satSolver.h"
#include <vector>
#include <set>
#include <algorithm>
#include <iterator>
#include <cstdio>
#include <cstdlib>

typedef std::vector<int> KlCut_t;          // 一個 cut = 排序好的 node ID
typedef std::vector<KlCut_t> KlCutSet_t;   // 一個節點的所有 cut

// 一個 KL cut 的完整資訊
struct KlResult {
    std::vector<int> V;   // roots  (遞增)
    std::vector<int> U;   // leaves (遞增)
    int size;             // |V| + |I|
};

// ---------------------------------------------------------------------------
// Step 1a：計算每個節點的 k-feasible cuts（沿用 PA1 的做法）
// ---------------------------------------------------------------------------
static KlCut_t KlMerge(const KlCut_t& a, const KlCut_t& b, int k) {
    KlCut_t r;
    std::set_union(a.begin(), a.end(), b.begin(), b.end(), std::back_inserter(r));
    if ((int)r.size() > k) r.clear();          // 超過 k 個 → 不合法
    return r;
}

static std::vector<KlCutSet_t> KlComputeCuts(Abc_Ntk_t* pNtk, int k) {
    std::vector<KlCutSet_t> cuts(Abc_NtkObjNumMax(pNtk));
    Abc_Obj_t* pObj;
    int i;
    // PI：只有自己
    Abc_NtkForEachPi(pNtk, pObj, i)
        cuts[Abc_ObjId(pObj)].push_back(KlCut_t(1, Abc_ObjId(pObj)));
    // AND 節點：ID 由小到大就是拓撲順序
    Abc_NtkForEachNode(pNtk, pObj, i) {
        int id = Abc_ObjId(pObj);
        cuts[id].push_back(KlCut_t(1, id));   // trivial cut {id}
        KlCutSet_t& c0 = cuts[Abc_ObjFaninId0(pObj)];
        KlCutSet_t& c1 = cuts[Abc_ObjFaninId1(pObj)];
        for (size_t a = 0; a < c0.size(); ++a)
            for (size_t b = 0; b < c1.size(); ++b) {
                KlCut_t m = KlMerge(c0[a], c1[b], k);
                if (m.empty()) continue;
                if (std::find(cuts[id].begin(), cuts[id].end(), m) == cuts[id].end())
                    cuts[id].push_back(m);
            }
    }
    return cuts;
}

// ---------------------------------------------------------------------------
// Step 1c：檢查 (K1)~(K4)，合法的話回傳 true 並算出 interior
// ---------------------------------------------------------------------------
static bool KlIn(const std::vector<int>& s, int id) {
    return std::find(s.begin(), s.end(), id) != s.end();
}

static bool KlCheck(Abc_Ntk_t* pNtk, const std::vector<int>& V, const std::vector<int>& U,
                    std::vector<int>& interior) {
    interior.clear();
    // (K1) U 與 V 不能相交（大小在列舉時已經保證）
    for (int v : V) if (KlIn(U, v)) return false;

    // (K2) 從 V 往 PI 走，遇到 leaf 就停。走到不是 leaf 的 PI → 不是 cut
    std::vector<int> reached;                       // 有被走到的 leaves
    std::vector<Abc_Obj_t*> stack;
    Abc_NtkIncrementTravId(pNtk);
    for (int v : V) {
        Abc_Obj_t* p = Abc_NtkObj(pNtk, v);
        Abc_NodeSetTravIdCurrent(p);
        stack.push_back(p);
    }
    while (!stack.empty()) {
        Abc_Obj_t* p = stack.back(); stack.pop_back();
        Abc_Obj_t* pFanin; int j;
        Abc_ObjForEachFanin(p, pFanin, j) {
            if (Abc_NodeIsTravIdCurrent(pFanin)) continue;
            Abc_NodeSetTravIdCurrent(pFanin);
            int id = Abc_ObjId(pFanin);
            if (KlIn(U, id)) { reached.push_back(id); continue; }   // 碰到 leaf：停
            if (Abc_ObjIsPi(pFanin)) return false;                  // 繞過所有 leaf 走到 PI
            if (Abc_ObjFaninNum(pFanin) == 0) continue;             // 常數節點
            if (!KlIn(V, id)) interior.push_back(id);               // 不是 root 就是 interior
            stack.push_back(pFanin);
        }
    }

    // (K3) 每個 leaf 都要 (a) 被上面的走訪碰到 (b) 自己有一條避開其他 leaf 的路到 PI
    for (int u : U) {
        if (!KlIn(reached, u)) return false;                         // (a)
        Abc_Obj_t* pU = Abc_NtkObj(pNtk, u);
        if (Abc_ObjIsPi(pU)) continue;                               // u 本身是 PI：(b) 成立
        bool found = false;
        Abc_NtkIncrementTravId(pNtk);
        stack.clear();
        stack.push_back(pU);
        Abc_NodeSetTravIdCurrent(pU);
        while (!stack.empty() && !found) {
            Abc_Obj_t* p = stack.back(); stack.pop_back();
            Abc_Obj_t* pFanin; int j;
            Abc_ObjForEachFanin(p, pFanin, j) {
                if (Abc_NodeIsTravIdCurrent(pFanin)) continue;
                Abc_NodeSetTravIdCurrent(pFanin);
                if (KlIn(U, Abc_ObjId(pFanin))) continue;           // 別的 leaf 擋住
                if (Abc_ObjIsPi(pFanin)) { found = true; break; }
                stack.push_back(pFanin);
            }
        }
        if (!found) return false;                                    // (b)
    }

    // (K4) interior 的每個 fanout 都必須是 interior 或 root，而且不能接到 PO
    Abc_NtkIncrementTravId(pNtk);
    for (int n : interior) Abc_NodeSetTravIdCurrent(Abc_NtkObj(pNtk, n));
    for (int n : interior) {
        Abc_Obj_t* pFanout; int j;
        Abc_ObjForEachFanout(Abc_NtkObj(pNtk, n), pFanout, j) {
            if (Abc_ObjIsPo(pFanout)) return false;
            if (Abc_NodeIsTravIdCurrent(pFanout)) continue;          // interior
            if (KlIn(V, Abc_ObjId(pFanout))) continue;               // root
            return false;                                            // 訊號漏出 cut
        }
    }
    return true;
}

// ---------------------------------------------------------------------------
// Step 1b：從 l 個不同的 root 各挑一個 cut，取聯集當作候選 U
// ---------------------------------------------------------------------------
struct KlEnum {
    Abc_Ntk_t* pNtk;
    int k, l;
    std::vector<int> nodes;                          // 所有 AND 節點 ID（遞增）
    std::vector<KlCutSet_t>* cuts;
    std::set<std::pair<std::vector<int>, std::vector<int> > > seen;   // 去重
    std::vector<KlResult> best;                      // 目前最大的 KL cuts
    int bestSize;
    long nKl;                                        // KL cut 總數（debug 用）
    bool verbose;
};

static void KlTry(KlEnum& E, const std::vector<int>& V, const std::vector<int>& U) {
    if (!E.seen.insert(std::make_pair(V, U)).second) return;        // 看過了
    std::vector<int> interior;
    if (!KlCheck(E.pNtk, V, U, interior)) return;
    int size = (int)V.size() + (int)interior.size();
    E.nKl++;
    if (E.verbose) {
        for (size_t i = 0; i < V.size(); ++i) printf(i ? " %d" : "%d", V[i]);
        printf(":");
        for (int u : U) printf(" %d", u);
        printf("   size = %d\n", size);
    }
    if (size < E.bestSize) return;
    if (size > E.bestSize) { E.bestSize = size; E.best.clear(); }
    KlResult r; r.V = V; r.U = U; r.size = size;
    E.best.push_back(r);
}

static void KlDfs(KlEnum& E, size_t start, std::vector<int>& V, const std::vector<int>& U) {
    if (!V.empty()) KlTry(E, V, U);
    if ((int)V.size() == E.l) return;
    for (size_t idx = start; idx < E.nodes.size(); ++idx) {
        int v = E.nodes[idx];
        const KlCutSet_t& cs = (*E.cuts)[v];
        for (size_t c = 0; c < cs.size(); ++c) {
            if (cs[c].size() == 1 && cs[c][0] == v) continue;        // 跳過 trivial cut {v}
            KlCut_t Unew;
            std::set_union(U.begin(), U.end(), cs[c].begin(), cs[c].end(), std::back_inserter(Unew));
            if ((int)Unew.size() > E.k) continue;                    // leaves 太多
            V.push_back(v);
            KlDfs(E, idx + 1, V, Unew);
            V.pop_back();
        }
    }
}

// ---------------------------------------------------------------------------
// Step 2：建 miter 的 CNF，用 SAT 算出每個 u 的 A(u)
// ---------------------------------------------------------------------------
static void KlAddAnd(sat_solver* s, int y, lit a, lit b) {          // y = a & b
    lit c[3];
    c[0] = toLitCond(y, 1); c[1] = a;                     sat_solver_addclause(s, c, c + 2);
    c[0] = toLitCond(y, 1); c[1] = b;                     sat_solver_addclause(s, c, c + 2);
    c[0] = toLit(y);        c[1] = lit_neg(a); c[2] = lit_neg(b); sat_solver_addclause(s, c, c + 3);
}

static void KlAddXor(sat_solver* s, int d, lit a, lit b) {          // d = a ^ b
    lit c[3];
    c[0] = toLitCond(d, 1); c[1] = a;         c[2] = b;         sat_solver_addclause(s, c, c + 3);
    c[0] = toLitCond(d, 1); c[1] = lit_neg(a); c[2] = lit_neg(b); sat_solver_addclause(s, c, c + 3);
    c[0] = toLit(d);        c[1] = lit_neg(a); c[2] = b;         sat_solver_addclause(s, c, c + 3);
    c[0] = toLit(d);        c[1] = a;         c[2] = lit_neg(b); sat_solver_addclause(s, c, c + 3);
}

static void KlComputeFlex(Abc_Ntk_t* pNtk, const KlResult& R) {
    int n = (int)R.U.size(), m = (int)R.V.size();
    int nObjs = Abc_NtkObjNumMax(pNtk);
    std::vector<int> varC(nObjs, -1);   // copy C  的變數
    std::vector<int> varD(nObjs, -1);   // copy C' 的變數（不受影響的節點跟 C 共用）
    std::vector<int> varP(m, -1);       // 新的 PI p_j（取代 root v_j）
    int nVars = 0;
    Abc_Obj_t* pObj; int i;

    // 先分配變數編號
    Abc_Obj_t* pConst = Abc_AigConst1(pNtk);
    varC[Abc_ObjId(pConst)] = varD[Abc_ObjId(pConst)] = nVars++;
    Abc_NtkForEachPi(pNtk, pObj, i) varC[Abc_ObjId(pObj)] = varD[Abc_ObjId(pObj)] = nVars++;
    Abc_NtkForEachNode(pNtk, pObj, i) {
        int id = Abc_ObjId(pObj);
        varC[id] = nVars++;
        int jRoot = (int)(std::find(R.V.begin(), R.V.end(), id) - R.V.begin());
        if (jRoot < m) { varD[id] = varP[jRoot] = nVars++; continue; }       // root → p_j
        bool same = varD[Abc_ObjFaninId0(pObj)] == varC[Abc_ObjFaninId0(pObj)] &&
                    varD[Abc_ObjFaninId1(pObj)] == varC[Abc_ObjFaninId1(pObj)];
        varD[id] = same ? varC[id] : nVars++;                                 // 不在 V 的 TFO → 共用
    }
    std::vector<int> varXor;
    Abc_NtkForEachPo(pNtk, pObj, i) {
        int drv = Abc_ObjFaninId0(pObj);
        if (varC[drv] != varD[drv]) varXor.push_back(nVars++);
    }
    int varMu = nVars++;

    sat_solver* s = sat_solver_new();
    sat_solver_setnvars(s, nVars);
    lit c[1];
    c[0] = toLit(varC[Abc_ObjId(pConst)]); sat_solver_addclause(s, c, c + 1);   // 常數 1

    // AND 節點的 clause（C 與 C' 各一份；共用的節點不重複加）
    Abc_NtkForEachNode(pNtk, pObj, i) {
        int id = Abc_ObjId(pObj), f0 = Abc_ObjFaninId0(pObj), f1 = Abc_ObjFaninId1(pObj);
        int c0 = Abc_ObjFaninC0(pObj), c1 = Abc_ObjFaninC1(pObj);
        KlAddAnd(s, varC[id], toLitCond(varC[f0], c0), toLitCond(varC[f1], c1));
        bool isRoot = std::find(R.V.begin(), R.V.end(), id) != R.V.end();
        if (!isRoot && varD[id] != varC[id])
            KlAddAnd(s, varD[id], toLitCond(varD[f0], c0), toLitCond(varD[f1], c1));
    }
    // 每對 PO 做 XOR，全部 OR 成 mu
    int x = 0;
    Abc_NtkForEachPo(pNtk, pObj, i) {
        int drv = Abc_ObjFaninId0(pObj), cpl = Abc_ObjFaninC0(pObj);
        if (varC[drv] == varD[drv]) continue;                        // 兩邊一定相同
        KlAddXor(s, varXor[x++], toLitCond(varC[drv], cpl), toLitCond(varD[drv], cpl));
    }
    std::vector<lit> orCl;                                           // mu -> (d1 + d2 + ...)
    orCl.push_back(toLitCond(varMu, 1));
    for (int d : varXor) orCl.push_back(toLit(d));
    sat_solver_addclause(s, &orCl[0], &orCl[0] + orCl.size());
    for (int d : varXor) {                                           // d_i -> mu
        lit cl[2] = { toLitCond(d, 1), toLit(varMu) };
        sat_solver_addclause(s, cl, cl + 2);
    }

        // 輸出：<V>: <U>: F_0 ... F_{2^n-1}
    for (int j = 0; j < m; ++j) printf(j ? " %d" : "%d", R.V[j]);
    printf(":");
    for (int u : R.U) printf(" %d", u);
    printf(":");

    std::vector<lit> assump(n + m + 1);
    for (int u = 0; u < (1 << n); ++u) {
        for (int t = 0; t < n; ++t) {                                // U = u（第一個 leaf 是 MSB）
            int bit = (u >> (n - 1 - t)) & 1;
            assump[t] = toLitCond(varC[R.U[t]], !bit);
        }
        unsigned mask = 0;
        // 問題 1：u 會不會出現？
        if (sat_solver_solve(s, &assump[0], &assump[0] + n, 0, 0, 0, 0) == l_False) {
            mask = (1u << (1 << m)) - 1;                             // SDC：全部都可以
        } else {
            // 問題 2：對每個 c，是否存在 x 讓 U=u 且強制成 c 會改變 PO？
            for (int cv = 0; cv < (1 << m); ++cv) {
                for (int j = 0; j < m; ++j) {
                    int bit = (cv >> (m - 1 - j)) & 1;
                    assump[n + j] = toLitCond(varP[j], !bit);
                }
                assump[n + m] = toLit(varMu);
                if (sat_solver_solve(s, &assump[0], &assump[0] + n + m + 1, 0, 0, 0, 0) == l_False)
                    mask |= 1u << cv;                                // UNSAT → c ∈ A(u)
            }
        }
        printf(" %X", mask);
    }
    printf("\n");
    
    sat_solver_delete(s);
}

// ---------------------------------------------------------------------------
// 指令介面
// ---------------------------------------------------------------------------
int Lsv_CommandKlFlex(Abc_Frame_t* pAbc, int argc, char** argv) {
    Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
    int c, k, l;
    bool verbose = false;
    Extra_UtilGetoptReset();
    while ((c = Extra_UtilGetopt(argc, argv, "vh")) != EOF) {
        switch (c) {
            case 'v': verbose = true; break;
            default: goto usage;
        }
    }
    if (pNtk == NULL) { Abc_Print(-1, "Empty network.\n"); return 1; }
    if (!Abc_NtkIsStrash(pNtk)) { Abc_Print(-1, "Please run \"strash\" first.\n"); return 1; }
    if (argc - globalUtilOptind != 2) goto usage;
    k = atoi(argv[globalUtilOptind]);
    l = atoi(argv[globalUtilOptind + 1]);
    if (k < 1 || l < 1) goto usage;

    {
        std::vector<KlCutSet_t> cuts = KlComputeCuts(pNtk, k);       // Step 1a
        KlEnum E;
        E.pNtk = pNtk; E.k = k; E.l = l; E.cuts = &cuts;
        E.bestSize = 0; E.nKl = 0; E.verbose = verbose;
        Abc_Obj_t* pObj; int i;
        Abc_NtkForEachNode(pNtk, pObj, i) E.nodes.push_back(Abc_ObjId(pObj));
        std::vector<int> V, U;
        KlDfs(E, 0, V, U);                                           // Step 1b + 1c
        if (verbose) printf("#KL cuts = %ld, max size = %d, #max = %d\n",
                            E.nKl, E.bestSize, (int)E.best.size());

        // ---- Step 1c 暫時輸出：印出最大的 KL cuts，Step 2 會換成 flexibility ----
        for (size_t r = 0; r < E.best.size(); ++r)                   // Step 2
            KlComputeFlex(pNtk, E.best[r]);
    }
    return 0;

usage:
    Abc_Print(-2, "usage: lsv_kl_flex [-vh] <k> <l>\n");
    Abc_Print(-2, "\t        prints the flexibility of every maximum KL cut\n");
    Abc_Print(-2, "\t-v    : also print every KL cut and its size (debug)\n");
    Abc_Print(-2, "\t-h    : print the command usage\n");
    return 1;
}