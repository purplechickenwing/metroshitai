// main2.cpp - Decoder for metro map

#include <bits/stdc++.h>
using namespace std;

struct Point {
    int x, y;
    bool operator==(const Point& other) const {
        return x == other.x && y == other.y;
    }
};

int dx[4] = {1, -1, 0, 0}; // R, L, D, U
int dy[4] = {0, 0, 1, -1};
string move_str[4] = {"R", "L", "D", "U"};

int main(int argc, char* argv[]) {
    if (argc != 4) {
        cerr << "Usage: " << argv[0] << " input.city input.satoutput output.metromap" << endl;
        return 1;
    }

    ifstream city_in(argv[1]);
    ifstream sat_in(argv[2]);
    ofstream out(argv[3]);

    int scenario;
    city_in >> scenario;

    int N, M, K, J;
    city_in >> N >> M >> K >> J;

    int P = 0;
    if (scenario == 2) {
        city_in >> P;
    }

    vector<Point> starts(K), ends(K);
    for (int k = 0; k < K; k++) {
        int sx, sy, ex, ey;
        city_in >> sx >> sy >> ex >> ey;
        starts[k] = {sx, sy};
        ends[k] = {ex, ey};
    }

    // Skip popular
    if (scenario == 2) {
        for (int p = 0; p < P*2; p++) {
            int tmp;
            city_in >> tmp;
        }
    }

    // Read sat output
    string sat_status;
    sat_in >> sat_status;
    if (sat_status == "UNSAT") {
        out << "0" << endl;
        return 0;
    }

    // Recompute var allocation to get E_vars
    int max_path = N * M;
    int B = 0;
    while ((1LL << B) <= max_path) B++;
    B++;

    int C = N * M;

    vector<Point> cells;
    for (int y = 0; y < M; y++) for (int x = 0; x < N; x++) cells.push_back({x, y});

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

    int var_cnt = 0;
    int first_E = var_cnt + 1;
    int E_size = K * DE;
    var_cnt += E_size;

    int first_O = var_cnt + 1;
    var_cnt += K * C;

    int first_R = var_cnt + 1;
    var_cnt += K * C * B;

    int first_Turn = var_cnt + 1;
    var_cnt += K * C;

    int first_S = var_cnt + 1;
    var_cnt += K * C * (J + 1);

    int first_Carry = var_cnt + 1;
    var_cnt += K * DE * (B - 1);

    int num_vars = var_cnt;

    auto E_var = [&](int k, int eid) { return first_E + k * DE + eid; };

    vector<bool> is_true(num_vars + 1, false);

    int lit;
    while (sat_in >> lit) {
        if (lit > 0) {
            is_true[lit] = true;
        } else if (lit < 0) {
            is_true[-lit] = false;
        }
    }

    // Now extract paths
    for (int k = 0; k < K; k++) {
        Point curr = starts[k];
        stringstream ss;
        bool reached = false;

        while (!(curr == ends[k])) {
            bool found = false;
            for (int d = 0; d < 4; d++) {
                int ed = edge_id[curr.x][curr.y][d];
                if (ed != -1) {
                    int ev = E_var(k, ed);
                    if (is_true[ev]) {
                        ss << move_str[d] << " ";
                        curr.x += dx[d];
                        curr.y += dy[d];
                        found = true;
                        break;
                    }
                }
            }
            if (!found) {
                // Error, but assume sat correct
                break;
            }
        }

        ss << "0";
        out << ss.str() << endl;
    }

    return 0;
}
