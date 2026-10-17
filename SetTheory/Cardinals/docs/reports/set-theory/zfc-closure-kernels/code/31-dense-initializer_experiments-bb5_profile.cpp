#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <vector>

// Marxen--Buntrock's published orientation (Marxen, simmbL5_1-m.html).
// Each transition writes, moves, then changes state; H is state 5.
struct Action { unsigned char write; int move; int next; };
int main(int argc, char** argv) {
    const Action table[5][2] = {
        {{1,-1,1},{1,1,2}}, {{1,-1,2},{1,-1,1}},
        {{1,-1,3},{0,1,4}}, {{1,1,0},{1,1,3}},
        {{1,-1,5},{0,1,0}}
    };
    constexpr int origin = 1000000;
    std::vector<unsigned char> tape(2*origin+1, 0);
    int head = origin, q = 0, low = head, high = head;
    std::uint64_t steps = 0;
    while (q != 5 && steps < 50000000) {
        if (head <= 0 || head >= int(tape.size())-1)
            throw std::runtime_error("finite simulation boundary reached");
        const auto a = table[q][tape[head]];
        tape[head] = a.write; head += a.move; q = a.next; ++steps;
        low = std::min(low,head); high = std::max(high,head);
    }
    if (q != 5) throw std::runtime_error("step bound exceeded");
    std::ofstream out(argc > 1 ? argv[1] : "bb5_profile.json");
    out << "{\"steps\":" << steps << ",\"state\":" << q
        << ",\"head\":" << head-origin << ",\"visited_min\":" << low-origin
        << ",\"visited_max\":" << high-origin << ",\"ones\":[";
    bool first = true;
    for (int i=0;i<int(tape.size());++i) if (tape[i]) {
        if (!first) out << ','; first=false; out << i-origin;
    }
    out << "]}\n";
}
