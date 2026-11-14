#include <algorithm>
#include <array>
#include <bitset>
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
vector<int> contexts[256][2];
int proj(int s, int drop, int keep) { return s == drop ? keep : s; }
bool run(int drop, int keep, int q, int b, int mask, int patch, Row changed,
         bitset<512> *visited) {
  auto old = tab[q][b];
  int goal = (mask & ~4) | (old.w << 2), goalhead = old.d,
      goalstate = proj(old.t, drop, keep);
  int state = proj(q, drop, keep), head = 0, tape = mask;
  for (int i = 0; i < 16; i++) {
    if (state >= N || head < -2 || head > 2)
      return false;
    int read = (tape >> (head + 2)) & 1;
    int key = state * 2 + read;
    if (visited)
      visited->set(key);
    Row row = (key == patch) ? changed : tab[state][read];
    tape = (tape & ~(1 << (head + 2))) | (row.w << (head + 2));
    head += row.d;
    state = proj(row.t, drop, keep);
    if (state == goalstate && head == goalhead && tape == goal)
      return true;
  }
  return false;
}
int main(int argc, char **argv) {
  if (argc != 5 && argc != 7)
    return 2;
  N = stoi(argv[4]);
  if (N <= 0 || N > 255)
    return 3;
  int onlydrop = argc == 7 ? stoi(argv[5]) : -1,
      onlykeep = argc == 7 ? stoi(argv[6]) : -1;
  if (argc == 7 && (onlydrop < 0 || onlydrop >= N || onlykeep < 0 ||
                    onlykeep >= N || onlydrop == onlykeep))
    return 3;
  ifstream tf(argv[1]), cf(argv[2]);
  ofstream out(argv[3]);
  if (!tf || !cf || !out)
    return 4;
  int q, b, w, t, nrows = 0;
  string d;
  bool rowseen[256][2] = {};
  while (tf >> q >> b >> w >> d >> t) {
    if (q < 0 || q >= N || b < 0 || b > 1 || w < 0 || w > 1 ||
        (d != "L" && d != "R") || t < 0 || t > N || rowseen[q][b])
      return 5;
    rowseen[q][b] = true;
    tab[q][b] = {w, d == "R" ? 1 : -1, t};
    nrows++;
  }
  if (!tf.eof() || nrows != 2 * N)
    return 5;
  int mask;
  while (cf >> q >> b >> mask) {
    if (q < 0 || q >= N || b < 0 || b > 1 || mask < 0 || mask >= 32 ||
        ((mask >> 2) & 1) != b)
      return 6;
    contexts[q][b].push_back(mask);
  }
  if (!cf.eof())
    return 6;
  int64_t pairs = 0, plain = 0, keys = 0, helperkeys = 0, patched = 0,
          firstpass = 0, success = 0;
  auto begin = chrono::steady_clock::now();
  for (int drop = 0; drop < N; drop++) {
    for (int keep = 0; keep < N; keep++) {
      if (drop == keep || (onlydrop >= 0 && drop != onlydrop) ||
          (onlykeep >= 0 && keep != onlykeep))
        continue;
      pairs++;
      bitset<512> possible;
      possible.set();
      bool hadFailure = false;
      for (int orig : {drop, keep}) {
        for (int read : {0, 1}) {
          for (int win : contexts[orig][read]) {
            bitset<512> visited;
            if (!run(drop, keep, orig, read, win, -1, {}, &visited)) {
              hadFailure = true;
              possible &= visited;
              if (possible.none())
                break;
            }
          }
          if (possible.none())
            break;
        }
        if (possible.none())
          break;
      }
      if (!hadFailure) {
        plain++;
        continue;
      }
      if (possible.none())
        continue;
      for (int patch = 0; patch < 2 * N; patch++)
        if (possible.test(patch)) {
          keys++;
          int helper = patch / 2, helperread = patch % 2;
          if (helper != keep)
            helperkeys++;
          if (helper == drop)
            return 7;
          for (int dest = 0; dest <= N; dest++)
            if (dest != drop)
              for (int wr = 0; wr < 2; wr++)
                for (int dr : {-1, 1}) {
                  Row r{wr, dr, dest};
                  patched++;
                  bool ok = true;
                  int failq = -1, failb = -1, failmask = -1;
                  for (int orig : {drop, keep, helper}) {
                    for (int read : {0, 1}) {
                      if (!contexts[orig][read].empty() &&
                          !run(drop, keep, orig, read, contexts[orig][read][0],
                               patch, r, nullptr)) {
                        ok = false;
                        break;
                      }
                    }
                    if (!ok)
                      break;
                  }
                  if (!ok)
                    continue;
                  firstpass++;
                  for (int orig : {drop, keep, helper}) {
                    for (int read : {0, 1}) {
                      for (int win : contexts[orig][read]) {
                        if (!run(drop, keep, orig, read, win, patch, r,
                                 nullptr)) {
                          ok = false;
                          failq = orig;
                          failb = read;
                          failmask = win;
                          break;
                        }
                      }
                      if (!ok)
                        break;
                    }
                    if (!ok)
                      break;
                  }
                  if (!ok)
                    out << "rejected " << drop << ' ' << keep << ' ' << helper
                        << ' ' << helperread << ' ' << wr << ' ' << dr << ' '
                        << dest << ' ' << failq << ' ' << failb << ' '
                        << failmask << '\n';
                  if (ok) {
                    success++;
                    out << "SURVIVOR " << drop << ' ' << keep << ' ' << helper
                        << ' ' << helperread << ' ' << wr << ' ' << dr << ' '
                        << dest << '\n';
                    out.flush();
                  }
                }
        }
    }
    if (drop % 25 == 24)
      cerr << "done=" << drop + 1 << " pairs=" << pairs << " keys=" << keys
           << " helperkeys=" << helperkeys << " patches=" << patched
           << " survivors=" << success << " sec="
           << chrono::duration<double>(chrono::steady_clock::now() - begin)
                  .count()
           << '\n';
  }
  cout << "pairs " << pairs << " plain " << plain << " patch_keys " << keys
       << " helper_keys " << helperkeys << " patches " << patched
       << " representative_pass " << firstpass << " survivors " << success
       << '\n';
}
