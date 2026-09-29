// Exact packed-color breadth-first search. C++17, no external libraries.
// This checks finite witnesses; it does not prove the all-n generation theorem.
#include <cstdint>
#include <exception>
#include <iostream>
#include <stdexcept>
#include <string>
#include <sstream>
#include <utility>
#include <vector>

std::uint64_t power(std::uint64_t a, int n) {
    std::uint64_t r = 1;
    while (n-- > 0) r *= a;
    return r;
}
std::pair<int,int> split(int n) {
    int h = n/2;
    if (n%2) return {h,h+1};
    if (h%2 == 0) return {h-1,h+1};
    return {h-2,h+2};
}
std::uint32_t act(std::uint32_t color, const std::vector<int>& t) {
    std::uint32_t next = 0;
    for (std::size_t q=0; q<t.size(); ++q)
        next |= ((color >> (2*t[q])) & 3U) << (2*q);
    return next;
}
std::uint64_t search(int n, bool weak) {
    auto [a,b] = split(n);
    std::vector<int> p(n), s(n);
    for (int q=0; q<n; ++q) {
        p[q] = q<a ? (q+1)%a : a+(q-a+1)%b;
        s[q] = q;
    }
    s[0] = a;
    if (!weak) {
        s[n-1] = 0;
        if (a%2) std::swap(s[1],s[2]);
    }
    std::uint32_t tau = 0;
    for (int q=0; q<n; ++q) {
        unsigned c = q==0 ? 0U : (q<a ? 1U : (q==a ? 2U : 3U));
        tau |= c << (2*q);
    }
    const std::size_t space = std::size_t(1) << (2*n);
    std::vector<unsigned char> seen(space,0);
    std::vector<std::uint32_t> queue;
    queue.reserve(space);
    seen[tau]=1;
    queue.push_back(tau);
    for (std::size_t head=0; head<queue.size(); ++head) {
        auto color=queue[head];
        for (const auto* t : {&p,&s}) {
            auto next=act(color,*t);
            if (!seen[next]) { seen[next]=1; queue.push_back(next); }
        }
    }
    return queue.size();
}
int main(int argc, char** argv) {
    try {
        if (argc>2) throw std::invalid_argument("Usage: witness_bfs [endpoint]");
        int endpoint=argc>1 ? std::stoi(argv[1]) : 12;
        if (endpoint<7 || endpoint>12)
            throw std::invalid_argument("Endpoint must lie between 7 and 12 (memory guard).");
        std::vector<std::string> rows;
        for (int n=7; n<=endpoint; ++n) {
            auto [a,b]=split(n);
            const auto B=6*power(2,n)+4*(power(3,a)+power(3,b))-12*(power(2,a)+power(2,b))+12;
            const auto expected=power(4,n)-B+std::uint64_t(a*b);
            const auto actual=search(n,false);
            if (actual != expected) throw std::runtime_error("Witness mismatch at n="+std::to_string(n));
            std::ostringstream row;
            row << "    {\"n\": " << n << ", \"A\": " << a << ", \"B\": " << b
                << ", \"orbit_size\": " << actual << ", \"expected\": " << expected << "}";
            rows.push_back(row.str());
        }
        auto weak=search(7,true);
        if (weak>256) throw std::runtime_error("Weak-witness bound failed");
        // Emit a success record only after every check has completed.
        std::cout << "{\n  \"status\": \"PASS\",\n  \"encoding\": \"two bits per state; exact BFS\",\n  \"rows\": [\n";
        for (std::size_t i=0; i<rows.size(); ++i)
            std::cout << rows[i] << (i+1<rows.size() ? "," : "") << "\n";
        std::cout << "  ],\n  \"nonextremal_example_n7_orbit_size\": " << weak << "\n}\n";
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "FAIL: " << e.what() << '\n';
        return 1;
    }
}
