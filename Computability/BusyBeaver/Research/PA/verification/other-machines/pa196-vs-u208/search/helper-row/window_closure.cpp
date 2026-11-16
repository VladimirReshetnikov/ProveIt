#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Row {
  int w, d, t;
};
int main(int argc, char **argv) {
  if (argc != 3 && argc != 4)
    return 2;
  int r = stoi(argv[2]);
  if (r < 2 || r > 10)
    return 3;
  ifstream f(argv[1]);
  if (!f)
    return 4;
  Row T[196][2];
  bool seenrow[196][2] = {};
  int q, b, w, n;
  string d;
  while (f >> q >> b >> w >> d >> n) {
    if (q < 0 || q >= 196 || b < 0 || b > 1 || seenrow[q][b])
      return 5;
    seenrow[q][b] = true;
    T[q][b] = {w, d == "R" ? 1 : -1, n};
  }
  for (q = 0; q < 196; q++)
    for (b = 0; b < 2; b++)
      if (!seenrow[q][b])
        return 6;
  int width = 2 * r + 1;
  uint32_t stride = 1U << width, mask = stride - 1, mid = 1U << r;
  uint64_t total = uint64_t(196) * stride;
  vector<uint8_t> seen((total + 7) / 8, 0);
  vector<uint32_t> queue;
  queue.reserve(1000000);
  queue.push_back(0);
  seen[0] = 1;
  bool mayhalt = false, projected[196][32] = {};
  uint64_t target = 0;
  bool exact = false;
  for (size_t i = 0; i < queue.size(); i++) {
    uint32_t code = queue[i], state = code >> width, bits = code & mask,
             small = (bits >> (r - 2)) & 31;
    projected[state][small] = true;
    if (state == 184 && small == 6)
      target++;
    if (state == 184 && r == 8 && bits == 410)
      exact = true;
    Row a = T[state][(bits >> r) & 1];
    bits = (bits & ~mid) | (uint32_t(a.w) << r);
    if (a.t == 196) {
      mayhalt = true;
      continue;
    }
    for (uint32_t fresh = 0; fresh < 2; fresh++) {
      uint32_t next = (a.d == 1) ? ((bits >> 1) | (fresh << (width - 1)))
                                 : (((bits << 1) & mask) | fresh);
      uint32_t key = (uint32_t(a.t) << width) | next;
      uint8_t flag = 1U << (key & 7);
      if (!(seen[key >> 3] & flag)) {
        seen[key >> 3] |= flag;
        queue.push_back(key);
      }
    }
  }
  if (argc == 4) {
    ofstream out(argv[3]);
    if (!out)
      return 7;
    for (uint32_t code : queue) {
      uint32_t state = code >> width, bits = code & mask,
               small = (bits >> (r - 2)) & 31;
      if (state == 184 && small == 6)
        out << bits << '\n';
    }
  }
  int count = 0;
  for (int s = 0; s < 196; s++)
    for (int m = 0; m < 32; m++)
      if (projected[s][m])
        count++;
  cout << "radius " << r << " closure " << queue.size() << " projected "
       << count << " may_halt " << mayhalt << " state184_mask6 "
       << projected[184][6] << " full_contexts " << target << " target_mask410 "
       << exact << '\n';
}
