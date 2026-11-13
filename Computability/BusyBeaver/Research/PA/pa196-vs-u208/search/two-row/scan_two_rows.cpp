// Bounded two-row fold screen. See README.md for the proof boundary.
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Row {
  int w, d, t;
};
int N = 196;
Row tab[256][2];
vector<int> ctx[256][2];
int proj(int x, int drop, int keep) { return x == drop ? keep : x; }
// 0 impossible within bounded template, 1 definite match, 2 unknown until
// second patch fixed.
int run(int drop, int keep, Row p0, Row p1, bool unknown1, int q, int b,
        int tape) {
  auto o = tab[q][b];
  int goal = (tape & ~(1 << 2)) | (o.w << 2), gh = o.d,
      gt = proj(o.t, drop, keep);
  int pos = 0, state = keep, cur = tape;
  for (int k = 0; k < 16; k++) {
    if (state >= N || pos < -2 || pos > 2)
      return 0;
    int read = (cur >> (pos + 2)) & 1;
    Row r;
    if (state == keep) {
      if (read && unknown1)
        return 2;
      r = read ? p1 : p0;
    } else
      r = tab[state][read];
    cur = (cur & ~(1 << (pos + 2))) | (r.w << (pos + 2));
    pos += r.d;
    state = proj(r.t, drop, keep);
    if (state == gt && pos == gh && cur == goal)
      return 1;
  }
  return 0;
}
int main(int argc, char **argv) {
  if (argc != 5 && argc != 7)
    return 2;
  N = stoi(argv[4]);
  int onlydrop = argc == 7 ? stoi(argv[5]) : -1,
      onlykeep = argc == 7 ? stoi(argv[6]) : -1;
  if (N <= 0 || N > 255 ||
      (argc == 7 && (onlydrop < 0 || onlydrop >= N || onlykeep < 0 ||
                     onlykeep >= N || onlydrop == onlykeep)))
    return 5;
  ifstream tf(argv[1]), cf(argv[2]);
  ofstream out(argv[3]);
  if (!tf || !cf || !out)
    return 3;
  int q, b, w, t, rows = 0;
  string d;
  bool rowseen[256][2] = {};
  while (tf >> q >> b >> w >> d >> t) {
    if (q < 0 || q >= N || b < 0 || b > 1 || w < 0 || w > 1 ||
        (d != "L" && d != "R") || t < 0 || t > N || rowseen[q][b])
      return 4;
    tab[q][b] = {w, d == "R" ? 1 : -1, t};
    rowseen[q][b] = true;
    ++rows;
  }
  if (!tf.eof() || rows != 2 * N)
    return 4;
  int bits;
  while (cf >> q >> b >> bits) {
    if (q < 0 || q >= N || b < 0 || b > 1 || bits < 0 || bits >= 32 ||
        ((bits >> 2) & 1) != b)
      return 6;
    ctx[q][b].push_back(bits);
  }
  if (!cf.eof())
    return 6;
  int64_t c0 = 0, c0possible = 0, pairs = 0, prefilter = 0, good = 0;
  auto st = chrono::steady_clock::now();
  for (int drop = 0; drop < N; drop++) {
    for (int keep = 0; keep < N; keep++)
      if (drop != keep && (onlydrop < 0 || drop == onlydrop) &&
          (onlykeep < 0 || keep == onlykeep)) {
        for (int dest0 = 0; dest0 <= N; dest0++)
          if (dest0 != drop)
            for (int w0 = 0; w0 < 2; w0++)
              for (int d0 : {-1, 1}) {
                ++c0;
                Row p0{w0, d0, dest0};
                bool pass = true;
                for (int qq : {drop, keep}) {
                  for (int x : ctx[qq][0]) {
                    int r = run(drop, keep, p0, {}, true, qq, 0, x);
                    if (r == 0) {
                      pass = false;
                      break;
                    }
                  }
                  if (!pass)
                    break;
                }
                if (!pass)
                  continue;
                ++c0possible;
                for (int dest1 = 0; dest1 <= N; dest1++)
                  if (dest1 != drop)
                    for (int w1 = 0; w1 < 2; w1++)
                      for (int d1 : {-1, 1}) {
                        ++pairs;
                        Row p1{w1, d1, dest1};
                        bool ok = true;
                        // One representative for each q/read; all genuine folds
                        // must pass it.
                        for (int bb : {1, 0}) {
                          for (int qq : {drop, keep}) {
                            if (!ctx[qq][bb].empty() &&
                                run(drop, keep, p0, p1, false, qq, bb,
                                    ctx[qq][bb][0]) != 1) {
                              ok = false;
                              break;
                            }
                          }
                          if (!ok)
                            break;
                        }
                        if (!ok)
                          continue;
                        ++prefilter;
                        int failq = -1, failb = -1, failx = -1;
                        for (int bb : {1, 0}) {
                          for (int qq : {drop, keep}) {
                            for (int x : ctx[qq][bb]) {
                              if (run(drop, keep, p0, p1, false, qq, bb, x) !=
                                  1) {
                                ok = false;
                                failq = qq;
                                failb = bb;
                                failx = x;
                                break;
                              }
                            }
                            if (!ok)
                              break;
                          }
                          if (!ok)
                            break;
                        }
                        if (!ok) {
                          out << "rejected " << drop << ' ' << keep << ' ' << w0
                              << ' ' << d0 << ' ' << dest0 << ' ' << w1 << ' '
                              << d1 << ' ' << dest1 << ' ' << failq << ' '
                              << failb << ' ' << failx << '\n';
                        }
                        if (ok) {
                          ++good;
                          out << "SURVIVOR " << drop << ' ' << keep << ' ' << w0
                              << ' ' << d0 << ' ' << dest0 << ' ' << w1 << ' '
                              << d1 << ' ' << dest1 << '\n';
                          out.flush();
                        }
                      }
              }
      }
    if (drop % 20 == 19)
      cerr << "drop " << drop + 1 << " viable0 " << c0possible << " pairs "
           << pairs << " firstpass " << prefilter << " survivors " << good
           << " elapsed "
           << chrono::duration<double>(chrono::steady_clock::now() - st).count()
           << '\n';
  }
  cout << "initial-patch0 " << c0 << " viable " << c0possible << " pairs "
       << pairs << " firstpass " << prefilter << " survivors " << good << '\n';
}
