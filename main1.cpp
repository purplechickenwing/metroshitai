// main1.cpp - Encoder for SAT input

#include <bits/stdc++.h>
using namespace std;

struct Point {
    int x, y;
};

int dx[4] = {1, -1, 0, 0}; // R, L, D, U
int dy[4] = {0, 0, 1, -1};
string dirs = "RLDU";

int opp_dir(int d) {
    if (d == 0) return 1;
    if (d == 1) return 0;
    if (d == 2) return 3;
    if (d == 3) return 2;
    return -1;
}

int main(int argc, char* argv[]) {
    if (argc != 3) {
        cerr << "Usage: " << argv[0] << " input.city output.satinput" << endl;
        return 1;
    }

    ifstream in(argv[1]);
    ofstream out(argv[2]);

    int scenario;
    in >> scenario;

    int N, M, K, J;
    in >> N >> M >> K >> J;

    int P = 0;
    if (scenario == 2) {
        in >> P;
    }

    vector<Point> starts(K), ends(K);
    for (int k = 0; k < K; k++) {
        int sx, sy, ex, ey;
        in >> sx >> sy >> ex >> ey;
        starts[k] = {sx, sy};
        ends[k] = {ex, ey};
    }

    vector<Point> popular(P);
    if (scenario == 2) {
        for (int p = 0; p < P; p++) {
            int px, py;
            in >> px >> py;
            popular[p] = {px, py};
        }
    }

    // Calculate B for ranks
    int max_path = N * M;
    int B = 0;
    while ((1LL << B) <= max_path) B++;
    B++; // Safety

    // Cells
    int C = N * M;
    vector<Point> cells;
    for (int y = 0; y < M; y++) {
        for (int x = 0; x < N; x++) {
            cells.push_back({x, y});
        }
    }

    // Edge ids
    vector<vector<vector<int>>> edge_id(N, vector<vector<int>>(M, vector<int>(4, -1)));
    vector<Point> from_edge;
    vector<int> dir_edge;
    int DE = 0;
    for (int x = 0; x < N; x++) {
        for (int y = 0; y < M; y++) {
            for (int d = 0; d < 4; d++) {
                int nx = x + dx[d], ny = y + dy[d];
                if (nx >= 0 && nx < N && ny >= 0 && ny < M) {
                    edge_id[x][y][d] = DE;
                    from_edge.push_back({x, y});
                    dir_edge.push_back(d);
                    DE++;
                }
            }
        }
    }

    // Var allocation
    int var_cnt = 0;

    // E[k][eid]
    int first_E = var_cnt + 1;
    int E_size = K * DE;
    var_cnt += E_size;

    // O[k][cid]
    int first_O = var_cnt + 1;
    int O_size = K * C;
    var_cnt += O_size;

    // R[k][cid][b]
    int first_R = var_cnt + 1;
    int R_size = K * C * B;
    var_cnt += R_size;

    // Turn[k][cid]
    int first_Turn = var_cnt + 1;
    int Turn_size = K * C;
    var_cnt += Turn_size;

    // S[k][i][j] i=1 to C, j=1 to J+1
    int first_S = var_cnt + 1;
    int S_size = K * C * (J + 1);
    var_cnt += S_size;

    // Carry[k][eid][bb] bb=0 to B-2 (carry1 to carry(B-1))
    int first_Carry = var_cnt + 1;
    int Carry_size = K * DE * (B - 1);
    var_cnt += Carry_size;

    int num_vars = var_cnt;

    auto E_var = [&](int k, int eid) { return first_E + k * DE + eid; };

    auto cell_id = [&](Point p) { return p.y * N + p.x; };

    auto O_var = [&](int k, Point p) { return first_O + k * C + cell_id(p); };

    auto R_var = [&](int k, Point p, int b) { return first_R + k * C * B + cell_id(p) * B + b; };

    auto Turn_var = [&](int k, int cid) { return first_Turn + k * C + cid; };

    auto S_var = [&](int k, int ii, int jj) { return first_S + k * C * (J + 1) + ii * (J + 1) + (jj - 1); };

    auto Carry_var = [&](int k, int eid, int bb) { return first_Carry + k * DE * (B - 1) + eid * (B - 1) + bb; };

    vector<vector<int>> clauses;

    auto add_clause = [&](vector<int> cl) { clauses.push_back(cl); };

    // Constraints

    for (int k = 0; k < K; k++) {
        Point sk = starts[k], ek = ends[k];
        int sk_id = cell_id(sk), ek_id = cell_id(ek);

        // Force Turn false for sk and ek
        add_clause({ -Turn_var(k, sk_id) });
        add_clause({ -Turn_var(k, ek_id) });

        // in=0 at sk, out=0 at ek
        vector<int> in_sk, out_ek;
        for (int d = 0; d < 4; d++) {
            int nx = sk.x - dx[d], ny = sk.y - dy[d];
            if (nx >= 0 && nx < N && ny >= 0 && ny < M) {
                int ed = edge_id[nx][ny][d];
                int ev = E_var(k, ed);
                add_clause({ -ev });
                in_sk.push_back(ev);
            }
        }

        for (int d = 0; d < 4; d++) {
            int nx = ek.x + dx[d], ny = ek.y + dy[d];
            if (nx >= 0 && nx < N && ny >= 0 && ny < M) {
                int ed = edge_id[ek.x][ek.y][d];
                int ev = E_var(k, ed);
                add_clause({ -ev });
                out_ek.push_back(ev);
            }
        }

        // out=1 at sk
        vector<int> out_sk;
        for (int d = 0; d < 4; d++) {
            if (edge_id[sk.x][sk.y][d] != -1) {
                out_sk.push_back(E_var(k, edge_id[sk.x][sk.y][d]));
            }
        }
        add_clause(out_sk); // at least one
        for (size_t i = 0; i < out_sk.size(); i++) {
            for (size_t jj = i + 1; jj < out_sk.size(); jj++) {
                add_clause({ -out_sk[i], -out_sk[jj] });
            }
        }

        // in=1 at ek
        vector<int> in_ek;
        for (int d = 0; d < 4; d++) {
            int nx = ek.x - dx[d], ny = ek.y - dy[d];
            if (nx >= 0 && nx < N && ny >= 0 && ny < M) {
                int ed = edge_id[nx][ny][d];
                in_ek.push_back(E_var(k, ed));
            }
        }
        add_clause(in_ek); // at least one
        for (size_t i = 0; i < in_ek.size(); i++) {
            for (size_t jj = i + 1; jj < in_ek.size(); jj++) {
                add_clause({ -in_ek[i], -in_ek[jj] });
            }
        }

        // For all cells, in <=1, out <=1
        for (int cid = 0; cid < C; cid++) {
            Point c = cells[cid];

            vector<int> in_Es, out_Es;
            for (int d = 0; d < 4; d++) {
                int nx = c.x - dx[d], ny = c.y - dy[d];
                if (nx >= 0 && nx < N && ny >= 0 && ny < M) {
                    int ed = edge_id[nx][ny][d];
                    in_Es.push_back(E_var(k, ed));
                }
            }
            for (int d = 0; d < 4; d++) {
                if (edge_id[c.x][c.y][d] != -1) {
                    out_Es.push_back(E_var(k, edge_id[c.x][c.y][d]));
                }
            }

            // in <=1
            for (size_t i = 0; i < in_Es.size(); i++) {
                for (size_t jj = i + 1; jj < in_Es.size(); jj++) {
                    add_clause({ -in_Es[i], -in_Es[jj] });
                }
            }

            // out <=1
            for (size_t i = 0; i < out_Es.size(); i++) {
                for (size_t jj = i + 1; jj < out_Es.size(); jj++) {
                    add_clause({ -out_Es[i], -out_Es[jj] });
                }
            }

            // O constraints
            int o_v = O_var(k, c);
            vector<int> all_E;
            all_E.reserve(in_Es.size() + out_Es.size());
            all_E.insert(all_E.end(), in_Es.begin(), in_Es.end());
            all_E.insert(all_E.end(), out_Es.begin(), out_Es.end());

            vector<int> cl = { -o_v };
            for (int ev : all_E) cl.push_back(ev);
            add_clause(cl);

            for (int ev : all_E) {
                add_clause({ -ev, o_v });
            }

            // Middle cells: in == out
            if (cell_id(c) != sk_id && cell_id(c) != ek_id) {
                // if in=1 then out=1
                for (int iev : in_Es) {
                    vector<int> cl2 = { -iev };
                    for (int oev : out_Es) cl2.push_back(oev);
                    add_clause(cl2);
                }

                // if out=1 then in=1
                for (int oev : out_Es) {
                    vector<int> cl2 = { -oev };
                    for (int iev : in_Es) cl2.push_back(iev);
                    add_clause(cl2);
                }
            }

            // Turn constraints
            int t_v = Turn_var(k, cid);

            vector<int> idir_vars(4, 0);
            for (int d = 0; d < 4; d++) {
                int nx = c.x - dx[d], ny = c.y - dy[d];
                if (nx >= 0 && nx < N && ny >= 0 && ny < M) {
                    int ed = edge_id[nx][ny][d];
                    idir_vars[d] = E_var(k, ed);
                }
            }

            vector<int> odir_vars(4, 0);
            for (int d = 0; d < 4; d++) {
                int ed = edge_id[c.x][c.y][d];
                if (ed != -1) {
                    odir_vars[d] = E_var(k, ed);
                }
            }

            // Turn => in=1
            vector<int> cl_in = { -t_v };
            for (int iv : idir_vars) if (iv > 0) cl_in.push_back(iv);
            if (cl_in.size() > 1) add_clause(cl_in);

            // Turn => out=1
            vector<int> cl_out = { -t_v };
            for (int ov : odir_vars) if (ov > 0) cl_out.push_back(ov);
            if (cl_out.size() > 1) add_clause(cl_out);

            // Turn => ~ (IDir[d] and ODir[d]) for each d
            for (int d = 0; d < 4; d++) {
                int iv = idir_vars[d];
                int ov = odir_vars[d];
                if (iv > 0 && ov > 0) {
                    add_clause({ -t_v, -iv, -ov });
                }
            }

            // reverse
            for (int di = 0; di < 4; di++) {
                int iv = idir_vars[di];
                if (iv > 0) {
                    for (int do_ = 0; do_ < 4; do_++) {
                        if (di != do_) {
                            int ov = odir_vars[do_];
                            if (ov > 0) {
                                add_clause({ -iv, -ov, t_v });
                            }
                        }
                    }
                }
            }
        }

        // Rank constraints
        for (int eid = 0; eid < DE; eid++) {
            int e_v = E_var(k, eid);
            Point a = from_edge[eid];
            int d = dir_edge[eid];
            Point bb_ = {a.x + dx[d], a.y + dy[d]};
            int aid = cell_id(a);
            int bid = cell_id(bb_);

            // bit 0
            int ra0 = R_var(k, a, 0);
            int rb0 = R_var(k, bb_, 0);
            add_clause({ -e_v, rb0, ra0 });
            add_clause({ -e_v, -rb0, -ra0 });

            // carry1 = ra0
            if (B > 1) {
                int c1 = Carry_var(k, eid, 0);
                add_clause({ -e_v, -c1, ra0 });
                add_clause({ -e_v, c1, -ra0 });
            }

            // for bit 1 to B-1
            for (int bit = 1; bit < B; bit++) {
                int ra_bit = R_var(k, a, bit);
                int rb_bit = R_var(k, bb_, bit);
                int c_in = (bit == 1 && B == 1) ? 0 : Carry_var(k, eid, bit - 1);

                // xor clauses
                add_clause({ -e_v, ra_bit, c_in, -rb_bit }); // 0 0 1 bad
                add_clause({ -e_v, ra_bit, -c_in, rb_bit }); // 0 1 0
                add_clause({ -e_v, -ra_bit, c_in, rb_bit }); // 1 0 0
                add_clause({ -e_v, -ra_bit, -c_in, -rb_bit }); // 1 1 1

                // carry out
                if (bit < B - 1) {
                    int c_next = Carry_var(k, eid, bit);
                    add_clause({ -e_v, c_next, -ra_bit, -c_in });
                    add_clause({ -e_v, -c_next, ra_bit });
                    add_clause({ -e_v, -c_next, c_in });
                } else {
                    // no overflow
                    add_clause({ -e_v, -ra_bit, -c_in });
                }
            }
        }

        // Cardinality for turns
        // First for i=1 (cell 0)
        int x0 = Turn_var(k, 0);
        add_clause({ -S_var(k, 1, 1), x0 });
        add_clause({ -x0, S_var(k, 1, 1) });
        for (int j = 2; j <= J + 1; j++) {
            add_clause({ -S_var(k, 0, j) }); // wait, S[1][j]
            add_clause({ -S_var(k, 1, j) });
        }

        for (int ii = 1; ii < C; ii++) {
            int prev = ii - 1, curr = ii;
            int x = Turn_var(k, ii);

            // j=1
            add_clause({ -S_var(k, curr, 1), S_var(k, prev, 1), x });
            add_clause({ -S_var(k, prev, 1), S_var(k, curr, 1) });
            add_clause({ -x, S_var(k, curr, 1) });

            for (int j = 2; j <= J + 1; j++) {
                add_clause({ -S_var(k, curr, j), S_var(k, prev, j), S_var(k, prev, j - 1) });
                add_clause({ -S_var(k, curr, j), S_var(k, prev, j), x });
                add_clause({ -S_var(k, prev, j), S_var(k, curr, j) });
                add_clause({ -S_var(k, prev, j - 1), -x, S_var(k, curr, j) });
            }
        }

        // <=J
        add_clause({ -S_var(k, C - 1, J + 1) });
    }

    // Overlap
    for (int cid = 0; cid < C; cid++) {
        for (int k1 = 0; k1 < K; k1++) {
            for (int k2 = k1 + 1; k2 < K; k2++) {
                add_clause({ -O_var(k1, cells[cid]), -O_var(k2, cells[cid]) });
            }
        }
    }

    // Popular
    if (scenario == 2) {
        for (Point p : popular) {
            vector<int> cl;
            for (int k = 0; k < K; k++) {
                cl.push_back(O_var(k, p));
            }
            add_clause(cl);
        }
    }

    // Write SAT input
    out << "p cnf " << num_vars << " " << clauses.size() << endl;
    for (auto& cl : clauses) {
        for (int lit : cl) out << lit << " ";
        out << "0" << endl;
    }

    return 0;
}
