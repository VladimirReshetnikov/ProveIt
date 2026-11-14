// Exhaustive two-row local fold search with conservative visited-row pruning.
#include <bitset>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Row { int w, d, target; };
struct Patch { int key; Row row; };
int N;
Row table[256][2];
vector<int> contexts[256][2];
int project(int q, int drop, int keep) { return q == drop ? keep : q; }
bool run(int drop, int keep, int q, int read, int mask, Patch first,
         Patch second, bitset<512> *visited) {
  Row orig = table[q][read];
  int expected_tape = (mask & ~8) | (orig.w << 3);
  int expected_head = orig.d, expected_state = project(orig.target, drop, keep);
  int state = project(q, drop, keep), head = 0, tape = mask;
  for (int i = 0; i < 32; i++) {
    if (state >= N || head < -3 || head > 3) return false;
    int bit = (tape >> (head + 3)) & 1, key = 2 * state + bit;
    if (visited) visited->set(key);
    Row row = key == first.key ? first.row :
              key == second.key ? second.row : table[state][bit];
    tape = (tape & ~(1 << (head + 3))) | (row.w << (head + 3));
    head += row.d;
    state = project(row.target, drop, keep);
    if (state == expected_state && head == expected_head && tape == expected_tape)
      return true;
  }
  return false;
}
int main(int argc, char **argv) {
  if (argc != 5 && argc != 7) return 2;
  N = stoi(argv[4]);
  if (N <= 0 || N > 255) return 3;
  int only_drop = argc == 7 ? stoi(argv[5]) : -1;
  int only_keep = argc == 7 ? stoi(argv[6]) : -1;
  if (argc == 7 && (only_drop < 0 || only_drop >= N || only_keep < 0 ||
                    only_keep >= N || only_drop == only_keep)) return 3;
  ifstream tf(argv[1]), cf(argv[2]);
  ofstream out(argv[3]);
  if (!tf || !cf || !out) return 4;
  int q, b, w, target, nrows = 0; string d;
  bool seen[256][2] = {};
  while (tf >> q >> b >> w >> d >> target) {
    if (q < 0 || q >= N || b < 0 || b > 1 || w < 0 || w > 1 ||
        (d != "L" && d != "R") || target < 0 || target > N || seen[q][b]) return 5;
    seen[q][b] = true; table[q][b] = {w, d == "R" ? 1 : -1, target}; nrows++;
  }
  if (!tf.eof() || nrows != 2 * N) return 5;
  int mask;
  while (cf >> q >> b >> mask) {
    if (q < 0 || q >= N || b < 0 || b > 1 || mask < 0 || mask >= 128 ||
        ((mask >> 3) & 1) != b) return 6;
    contexts[q][b].push_back(mask);
  }
  if (!cf.eof()) return 6;
  Patch none{-1, {}};
  int64_t pairs = 0, first_keys = 0, first_patches = 0, second_keys = 0,
          second_patches = 0, passes = 0, plain = 0, one = 0;
  for (int drop = 0; drop < N; drop++) {
    for (int keep = 0; keep < N; keep++) {
      if (drop == keep || (only_drop >= 0 && drop != only_drop) ||
          (only_keep >= 0 && keep != only_keep)) continue;
      pairs++;
      bitset<512> minimum;
      size_t minimum_size = 513;
      for (int orig : {drop, keep}) for (int bit = 0; bit < 2; bit++)
        for (int win : contexts[orig][bit]) {
          bitset<512> visited;
          if (!run(drop, keep, orig, bit, win, none, none, &visited) &&
              visited.count() < minimum_size) {
            minimum = visited; minimum_size = visited.count();
          }
        }
      if (minimum_size == 513) { plain++; continue; }
      for (int key = 0; key < 2 * N; key++) if (minimum[key]) {
        first_keys++;
        for (int dest = 0; dest <= N; dest++) if (dest != drop)
          for (int wr = 0; wr < 2; wr++) for (int dr : {-1, 1}) {
            Patch first{key, {wr, dr, dest}}; first_patches++;
            bitset<512> possible; possible.set(); bool failure = false;
            for (int orig : {drop, keep, key / 2}) {
              for (int bit = 0; bit < 2; bit++) {
                for (int win : contexts[orig][bit]) {
                  bitset<512> visited;
                  if (!run(drop, keep, orig, bit, win, first, none, &visited)) {
                    failure = true; possible &= visited;
                    if (possible.none()) break;
                  }
                }
                if (possible.none()) break;
              }
              if (possible.none()) break;
            }
            if (!failure) {
              one++;
              out << "ONE " << drop << ' ' << keep << ' ' << key << ' '
                  << wr << ' ' << dr << ' ' << dest << '\n';
              continue;
            }
            possible[key] = false; possible[2 * drop] = false;
            possible[2 * drop + 1] = false;
            for (int key2 = 0; key2 < 2 * N; key2++) if (possible[key2]) {
              second_keys++;
              for (int dest2 = 0; dest2 <= N; dest2++) if (dest2 != drop)
                for (int wr2 = 0; wr2 < 2; wr2++) for (int dr2 : {-1, 1}) {
                  second_patches++;
                  Patch second{key2, {wr2, dr2, dest2}};
                  bool ok = true;
                  for (int orig : {drop, keep, key / 2, key2 / 2}) {
                    for (int bit = 0; bit < 2; bit++) {
                      for (int win : contexts[orig][bit])
                        if (!run(drop, keep, orig, bit, win, first, second, nullptr)) {
                          ok = false; break;
                        }
                      if (!ok) break;
                    }
                    if (!ok) break;
                  }
                  if (ok) {
                    passes++;
                    out << "PASS " << drop << ' ' << keep << ' ' << key << ' '
                        << wr << ' ' << dr << ' ' << dest << ' ' << key2 << ' '
                        << wr2 << ' ' << dr2 << ' ' << dest2 << '\n';
                  }
                }
            }
          }
      }
    }
  }
  cout << "pairs " << pairs << " plain " << plain << " first_keys " << first_keys
       << " first_patches " << first_patches << " one " << one << " second_keys "
       << second_keys << " second_patches " << second_patches << " passes " << passes << '\n';
}
