// Written by Melnik
// Created 12.03.2016

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <ctime>
#include <iomanip>
#include <vector>

using namespace std;


const int maxn = 100500;
const int inf = 2e9;
const double eps = 1e-8;
const int base = 1073676287;

int timer = 0;
int current_chain = 0;
vector <int> edge[maxn];
bool used[maxn];
int subtree_size[maxn];
int tin[maxn], tout[maxn];
int parent[maxn];
int chain_idx[maxn];                            // index of vertex chain
vector <int> chain_vertices_list[maxn];         // chains itself
vector <int> tree[maxn];                        // segment tree for each chain
int chain_size[maxn];           
int to_add[maxn];

void Init() {
    for (int i = 0; i < maxn; ++i)
        used[i] = to_add[i] = false;
}

void InitChain(int id) {
    int sz = chain_vertices_list[id].size();
    tree[id].assign(4 * sz, 0);
}

int Dfs(int v, int anc) {
    parent[v] = anc;
    used[v] = true;
    tin[v] = ++timer;
    subtree_size[v] = 1;
    int sz = edge[v].size();
    for (int i = 0; i < sz; ++i) {
        int to = edge[v][i];
        if (!used[to])
            subtree_size[v] += Dfs(to, v);
    }
    tout[v] = ++timer;
    return subtree_size[v];
}

void BuildChains(int v) {
    chain_vertices_list[chain_idx[v]].push_back(v);
    used[v] = true;
    int heavySz = (subtree_size[v] + 1) >> 1;
    int sz = edge[v].size();
    for (int i = 0; i < sz; ++i) {
        int to = edge[v][i];
        if (used[to])
            continue;
        if (subtree_size[to] >= heavySz)
            chain_idx[to] = chain_idx[v];
        else
            chain_idx[to] = ++current_chain;
        BuildChains(to);
    }
}

inline void Update(int id, int v, int tl, int tr, int pos, int cnt) {
    if (tl == tr) {
        tree[id][v] += cnt;
        return;
    }
    int newV = v << 1;
    int mid = (tl + tr) >> 1;
    if (pos <= mid)
        Update(id, newV, tl, mid, pos, cnt);
    else
        Update(id, newV + 1, mid + 1, tr, pos, cnt);
    tree[id][v] = max(tree[id][newV], tree[id][newV + 1]);
}

inline int FindMax(int id, int v, int tl, int tr, int l, int r) {
    if (l > r)
        return 0;
    if (tl == l && tr == r)
        return tree[id][v];
    int newV = v << 1;
    int mid = (tl + tr) >> 1;
    return max(FindMax(id, newV, tl, mid, l, min(r, mid)),
        FindMax(id, newV + 1, mid + 1, tr, max(mid + 1, l), r));
}

void Add(int v, int c) {
    int id = chain_idx[v];
    to_add[v] += c;
    int l, r;
    l = 0, r = chain_size[id] - 1;
    int needSz = subtree_size[v];
    while (r - l > 1) {
        int mid = (l + r) >> 1;
        if (subtree_size[chain_vertices_list[id][mid]] > needSz)
            l = mid + 1;
        else
            r = mid;
    }
    if (subtree_size[chain_vertices_list[id][l]] == needSz)
        v = l;
    else
        v = r;
    ++v;
    Update(id, 1, 1, chain_size[id], v, c);
}

inline bool IsNotAncestor(int v1, int v2) {
    return !(tin[v1] <= tin[v2] && tout[v1] >= tout[v2]);
}

int findV(int id, int v) {
    int l, r;
    l = 0;
    r = chain_size[id] - 1;
    while (r - l > 1) {
        int mid = (l + r) >> 1;
        if (subtree_size[chain_vertices_list[id][mid]] > subtree_size[v])
            l = mid + 1;
        else
            r = mid;
    }
    if (subtree_size[v] == subtree_size[chain_vertices_list[id][l]])
        return l;
    return r;
}

int FindNewVertix(int id, int v) {
    int l, r;
    l = 0;
    r = chain_size[id] - 1;
    while (r - l > 1) {
        int mid = (l + r) >> 1;
        if (!IsNotAncestor(chain_vertices_list[id][mid], v))
            l = mid;
        else
            r = mid - 1;
    }
    if (!IsNotAncestor(chain_vertices_list[id][r], v))
        return r;
    return l;
}

int Solve(int v1, int v2) {
    int c1 = chain_idx[v1];
    int c2 = chain_idx[v2];
    int ans = 0;
    if (v1 == v2)
        return to_add[v1];
    while (IsNotAncestor(v1, v2)) {         // lift up v1 while v2 is not in a subtree of v1
        c1 = chain_idx[v1];
        int pos1 = findV(c1, v1);
        int pos2 = FindNewVertix(c1, v2);
        ans = max(ans, FindMax(c1, 1, 1, chain_size[c1], pos2 + 1, pos1 + 1));
        int newV = chain_vertices_list[c1][pos2];
        if (!IsNotAncestor(newV, v2))
            v1 = newV;
        else
            v1 = parent[newV];
    }

    while (IsNotAncestor(v2, v1)) {         // lift up v2 while v1 is not in a subtree of v2
        c2 = chain_idx[v2];
        int pos1 = findV(c2, v2);
        int pos2 = FindNewVertix(c2, v1);
        ans = max(ans, FindMax(c2, 1, 1, chain_size[c2], pos2 + 1, pos1 + 1));
        int newV = chain_vertices_list[c2][pos2];
        if (!IsNotAncestor(newV, v1))
            v2 = newV;
        else
            v2 = parent[newV];
    }
    if (v1 == v2)
        ans = max(ans, to_add[v1]);
    return ans;
}

int main()
{
    // srand(time(NULL));
    // freopen("input.txt", "r", stdin);
    // freopen("output.txt", "w", stdout);
    // ios_base::sync_with_stdio(false);
    int n, q;
    scanf ("%d", &n);
    Init();
    for (int i = 1; i < n; ++i) {
        int x, y;
        scanf ("%d%d", &x, &y);
        edge[x].push_back(y);
        edge[y].push_back(x);
    }
    scanf ("%d\n", &q);
    subtree_size[1] = Dfs(1, -1);
    Init();
    chain_idx[1] = 0;
    BuildChains(1);
    for (int i = 0; i < maxn; ++i)
        chain_size[i] = chain_vertices_list[i].size();
    for (int i = 0; i < n; ++i) {
        if (chain_vertices_list[i].empty())
            break;
        InitChain(i);
    }
    while (q--) {
        char t;
        int x, y;
        scanf ("%c%d%d", &t, &x, &y);
        if (t == 'I')
            Add(x, y);
        else
            printf ("%d\n", Solve(x, y));
        if (q)
            scanf ("\n");
    }
    return 0;
}
