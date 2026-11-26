// Separate replay of the six-place computation. Input is a directory of
// finite-field columns made by independent_quintic.py.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Four = std::array<int, 4>;
using Columns = std::array<Four, 5>;
using Count = std::int64_t;

class RankTest {
public:
    explicit RankTest(int prime) : prime_(prime) {
        std::ifstream file(std::to_string(prime) + ".dat");
        if (!(file >> period_) || period_ <= 0) throw std::runtime_error("missing table");
        table_.resize(period_);
        for (Columns& columns : table_)
            for (Four& col : columns)
                for (int& entry : col)
                    if (!(file >> entry)) throw std::runtime_error("incomplete table");
    }
    void prepare(int a, int b, int c) {
        int i = a % period_, j = b % period_, k = c % period_;
        residues_ = {0, i, j, k};
        const Four& A = table_[i][i == 0];
        const Four& B = table_[j][(j == 0) + (i == j)];
        const Four& C = table_[k][(k == 0) + (i == k) + (j == k)];
        for (int d = 0; d < 4; ++d) {
            int x = (d+1)%4, y = (d+2)%4, z = (d+3)%4;
            Count cofactor =
                  Count(A[x]) * (Count(B[y])*C[z] - Count(B[z])*C[y])
                - Count(A[y]) * (Count(B[x])*C[z] - Count(B[z])*C[x])
                + Count(A[z]) * (Count(B[x])*C[y] - Count(B[y])*C[x]);
            normal_[d] = (d % 2 ? -1 : 1) * (cofactor % prime_);
        }
    }
    bool dependent(int d) const {
        int k = d % period_;
        int collisions = std::count(residues_.begin(), residues_.end(), k);
        const Four& col = table_[k][collisions];
        Count determinant = 0;
        for (int i = 0; i < 4; ++i) determinant += Count(normal_[i]) * col[i];
        return determinant % prime_ == 0;
    }
private:
    int prime_, period_;
    std::vector<Columns> table_;
    Four residues_, normal_;
};

std::vector<Four> step(const std::vector<Four>& survivors, int old_mod, int mod,
                       const std::vector<int>& primes, Count target, Count left) {
    std::vector<RankTest> tests;
    for (int p : primes) tests.emplace_back(p);
    std::vector<Four> next;
    Count examined = 0;
    for (const Four& s : survivors) {
        for (int a = s[0]; a < mod; a += old_mod)
            for (int b = (s[0]==s[1] ? a : s[1]); b < mod; b += old_mod)
                for (int c = (s[1]==s[2] ? b : s[2]); c < mod; c += old_mod) {
                    for (RankTest& t : tests) t.prepare(a,b,c);
                    for (int d = (s[2]==s[3] ? c : s[3]); d < mod; d += old_mod) {
                        ++examined;
                        bool survives = true;
                        for (const RankTest& t : tests)
                            if (!t.dependent(d)) { survives = false; break; }
                        if (survives) {
                            Four lift = {a,b,c,d};
                            std::sort(lift.begin(),lift.end());
                            next.push_back(lift);
                        }
                    }
                }
    }
    std::sort(next.begin(), next.end());
    if (std::adjacent_find(next.begin(), next.end()) != next.end() ||
        examined != target || Count(next.size()) != left)
        throw std::runtime_error("independent census disagrees");
    std::cout << mod << "  " << examined << "  " << next.size() << '\n';
    return next;
}

int main() {
    std::vector<Four> keep = {{0,0,0,0}};
    keep = step(keep,1,200,{601},68685050,119264);
    keep = step(keep,200,1400,{1051,4201},279218674,196);
    keep = step(keep,1400,4200,{6301},15876,5876);
    keep = step(keep,4200,12600,{757},475956,214120);
    keep = step(keep,12600,25200,{337},3425920,0);
}
