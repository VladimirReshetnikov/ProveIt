// Independent enumeration of all 8,408,566 lattice points in the 17-point example.
// C++17, no external libraries. The code does NOT use a gamma expansion,
// perfectly-matchable-set counts, root polytopes, or floating-point arithmetic.
// Build: c++ -O3 -std=c++17 code/direct_counterexample.cpp -o /tmp/direct_preorder
// Run:   /tmp/direct_preorder > data/direct_counterexample.json
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

static int popcount(unsigned value) {
    int count = 0;
    while (value) { value &= value - 1; ++count; }
    return count;
}

int main() {
    constexpr int p=9, q=8;
    constexpr std::array<unsigned,q> neighbors={1,3,7,15,31,62,252,504};
    constexpr std::array<std::uint64_t,18> expected={
        1,49,952,9828,61302,248816,688516,1337738,1857081,
        1857081,1337738,688516,248816,61302,9828,952,49,1};
    std::array<std::vector<unsigned>,p> destinations;
    for(int a=0;a<p;++a)
        for(int b=0;b<q;++b)
            if(neighbors[b]&(1u<<a)) destinations[a].push_back(1u<<(3*b));
    // Base eight is safe: every upper coordinate is at most degree(b)+1 <= 7.
    std::vector<std::uint16_t> seen(1u<<(3*q),0);
    std::uint16_t epoch=0;
    std::vector<unsigned> initial;
    for(unsigned mask=0;mask<(1u<<q);++mask) {
        unsigned code=0;
        for(int b=0;b<q;++b) if(mask&(1u<<b)) code|=1u<<(3*b);
        initial.push_back(code);
    }
    std::array<std::uint64_t,18> h{};
    for(unsigned zeros=0;zeros<(1u<<p);++zeros) {
        std::vector<unsigned> states=initial;
        for(int a=0;a<p;++a) if(zeros&(1u<<a)) {
            ++epoch;
            std::vector<unsigned> next;
            next.reserve(states.size()*3);
            auto insert=[&](unsigned value) {
                if(value>=seen.size()) throw std::runtime_error("Digit overflow");
                if(seen[value]!=epoch) { seen[value]=epoch; next.push_back(value); }
            };
            for(unsigned state:states) {
                insert(state); // this unit of unused lower capacity remains unused
                for(unsigned step:destinations[a]) insert(state+step);
            }
            states.swap(next);
        }
        int lower_support=p-popcount(zeros);
        for(unsigned state:states) {
            int support=lower_support;
            for(int b=0;b<q;++b) support+=((state>>(3*b))&7u)!=0;
            ++h[support];
        }
    }
    if(h!=expected) throw std::runtime_error("Direct lattice counts differ");
    std::uint64_t total=0;
    std::cout << "{\n  \"method\": \"integer capacity allocation, deduplicated\",\n"
              << "  \"h\": [";
    for(int i=0;i<=p+q;++i) {
        if(i) std::cout << ", ";
        std::cout << h[i]; total+=h[i];
    }
    std::cout << "],\n  \"total_lattice_points\": " << total
              << ",\n  \"all_tests_passed\": true\n}\n";
}
