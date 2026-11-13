// Finite blank-run block-simulation screen; not an infinite-run proof.
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
using namespace std;
struct Row {
  int write, dir, target;
};
static constexpr int N = 196, DROP = 45, KEEP = 160, HELPER = 184,
                     MAX_BLOCK = 512;
int project(int q) { return q == DROP ? KEEP : q; }
int block(const Row table[N][2], int source, int64_t head,
          const set<int64_t> &tape) {
  const Row original = table[source][tape.count(head) ? 1 : 0];
  const int goal_state = project(original.target);
  const int64_t goal_head = head + original.dir;
  map<int64_t, int> expected, delta;
  if (original.write != int(tape.count(head) > 0))
    expected[head] = original.write;
  int state = project(source);
  int64_t pos = head;
  for (int i = 0; i < MAX_BLOCK; i++) {
    if (state == N)
      return 0;
    auto it = delta.find(pos);
    int bit = it == delta.end() ? int(tape.count(pos) > 0) : it->second;
    Row row =
        (state == HELPER && bit == 1) ? Row{1, -1, 75} : table[state][bit];
    if (row.write == int(tape.count(pos) > 0))
      delta.erase(pos);
    else
      delta[pos] = row.write;
    pos += row.dir;
    state = project(row.target);
    if (state == goal_state && pos == goal_head && delta == expected)
      return i + 1;
  }
  return 0;
}
int main(int argc, char **argv) {
  if (argc != 3)
    return 2;
  ifstream file(argv[1]);
  if (!file)
    return 3;
  const int64_t budget = stoll(argv[2]);
  if (budget < 0)
    return 4;
  Row table[N][2];
  bool seen[N][2] = {};
  int q, b, w, n, count = 0;
  string d;
  while (file >> q >> b >> w >> d >> n) {
    if (q < 0 || q >= N || b < 0 || b > 1 || w < 0 || w > 1 ||
        (d != "L" && d != "R") || n < 0 || n > N || seen[q][b])
      return 5;
    seen[q][b] = true;
    table[q][b] = {w, d == "R" ? 1 : -1, n};
    count++;
  }
  if (!file.eof() || count != 2 * N)
    return 5;
  set<int64_t> tape;
  int state = 0;
  int64_t head = 0, child_steps = 0;
  array<int64_t, 3> visits{};
  array<int64_t, MAX_BLOCK + 1> lengths{};
  for (int64_t i = 0; i < budget; i++) {
    if (state == N) {
      cerr << "original halted at " << i << '\n';
      return 6;
    }
    if (state == DROP || state == KEEP || state == HELPER) {
      visits[state == DROP ? 0 : state == KEEP ? 1 : 2]++;
      int n = block(table, state, head, tape);
      if (n <= 0) {
        cerr << "block mismatch at parent step " << i << " state " << state
             << " head " << head << '\n';
        return 7;
      }
      lengths[n]++;
      child_steps += n;
    } else
      child_steps++;
    Row row = table[state][tape.count(head) ? 1 : 0];
    if (row.write)
      tape.insert(head);
    else
      tape.erase(head);
    head += row.dir;
    state = row.target;
  }
  cout << "parent_steps " << budget << " child_steps " << child_steps
       << " parent_state " << state << " parent_head " << head
       << " parent_ones " << tape.size() << " visits_45 " << visits[0]
       << " visits_160 " << visits[1] << " visits_184 " << visits[2]
       << " histogram";
  for (int n = 1; n <= MAX_BLOCK; n++)
    if (lengths[n])
      cout << ' ' << n << ':' << lengths[n];
  cout << '\n';
}
