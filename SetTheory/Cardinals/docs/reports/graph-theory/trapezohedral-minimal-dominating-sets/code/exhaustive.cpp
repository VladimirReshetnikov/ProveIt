// Independent exhaustive verification. No structural theorem is used here.
// Build: g++ -O3 -std=c++17 exhaustive.cpp -o exhaustive
// Run: ./exhaustive 11 > exhaustive.csv
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Mask = std::uint64_t;
static unsigned first(Mask x) {
  unsigned index = 0;
  while ((x & 1) == 0) { ++index; x >>= 1; }
  return index; // All callers supply x != 0.
}
static unsigned count(Mask x) {
  unsigned result = 0;
  while (x) { ++result; x &= x-1; }
  return result;
}

int main(int argc, char** argv) {
  try {
    const int maximum = argc > 1 ? std::stoi(argv[1]) : 10;
    if (maximum < 3 || maximum > 14)
      throw std::invalid_argument("maximum n must be in [3,14]; time grows exponentially");
    std::cout << "n,size,edges,mask\n";
    std::uint64_t examined = 0;
    for (int n = 3; n <= maximum; ++n) {
      const unsigned order = static_cast<unsigned>(2*n+2);
      std::vector<Mask> open(order, 0), closed(order, 0);
      auto a = [](int i) { return 2+2*i; };
      auto b = [](int i) { return 3+2*i; };
      auto edge = [&](int i, int j) { open[i] |= Mask(1)<<j; open[j] |= Mask(1)<<i; };
      for (int i = 0; i < n; ++i) {
        edge(0, a(i)); edge(1, b(i));
        edge(a(i), b(i)); edge(b(i), a((i+1)%n));
      }
      for (unsigned v = 0; v < order; ++v) closed[v] = open[v] | (Mask(1)<<v);
      std::uint64_t accepted = 0;
      const Mask limit = Mask(1)<<order;
      for (Mask d = 0; d < limit; ++d) {
        // Simultaneously test domination and the private-neighbor criterion.
        bool dominating = true;
        Mask has_private_neighbor = 0;
        for (unsigned w = 0; w < order; ++w) {
          const Mask hit = closed[w] & d;
          if (hit == 0) { dominating = false; break; }
          if ((hit & (hit-1)) == 0) has_private_neighbor |= hit;
        }
        if (!dominating || has_private_neighbor != d) continue;
        // A graph traversal checks induced connectivity independently.
        Mask seen = d & (~d+1), frontier = seen;
        while (frontier) {
          const unsigned v = first(frontier);
          frontier &= frontier-1;
          const Mask fresh = open[v] & d & ~seen;
          seen |= fresh; frontier |= fresh;
        }
        if (seen != d) continue;
        unsigned twice_edges = 0;
        for (Mask todo = d; todo; todo &= todo-1)
          twice_edges += count(open[first(todo)] & d);
        ++accepted;
        std::cout << n << ',' << count(d) << ',' << twice_edges/2 << ',' << d << '\n';
      }
      examined += limit;
      std::cerr << "n=" << n << " subsets=" << limit << " accepted=" << accepted << '\n';
    }
    std::cerr << "TOTAL_SUBSETS=" << examined << '\n';
    return 0;
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << '\n'; return 1;
  }
}
