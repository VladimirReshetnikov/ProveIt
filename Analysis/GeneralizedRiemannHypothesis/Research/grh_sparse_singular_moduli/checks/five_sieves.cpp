// Rank tests for five columns in a free algebra of dimension six.
// After pivoting on the distinguished column 1, four vectors of length five remain.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

using Quadruple = std::array<int, 4>;
using Column = std::array<int, 5>;
using Wide = std::int64_t;
using Set = std::vector<Quadruple>;

struct Place {
    int m, p;
    std::vector<std::array<Column, 5>> table;
    std::array<int, 5> residues{};
    int minors[5][5][5]{};

    Place(int discriminant, int prime) {
        std::ifstream in(std::to_string(discriminant) + "-" + std::to_string(prime) + ".txt");
        if (!(in >> m >> p) || m < 1 || p != prime) throw std::runtime_error("Bad table");
        table.resize(m);
        for (auto& block : table) for (auto& column : block) for (auto& z : column)
            if (!(in >> z) || z < 0 || z >= p) throw std::runtime_error("Bad coordinate");
    }

    const Column& column(int exponent, int i) {
        residues[i] = exponent % m;
        int j = std::count(residues.begin(), residues.begin() + i, residues[i]);
        return table[residues[i]][j];
    }

    void first_three(int a, int b, int c) {
        auto x = column(a, 1), y = column(b, 2), z = column(c, 3);
        Wide two[5][5]{};
        for (int i = 0; i < 5; ++i) for (int j = i+1; j < 5; ++j)
            two[i][j] = (Wide(x[i])*y[j] - Wide(x[j])*y[i]) % p;
        for (int i = 0; i < 5; ++i) for (int j = i+1; j < 5; ++j)
            for (int k = j+1; k < 5; ++k)
                minors[i][j][k] = (two[i][j]*z[k] - two[i][k]*z[j] + two[j][k]*z[i]) % p;
    }

    bool dependent(int d) {
        const auto& w = column(d, 4);
        // All four-by-four minors must vanish. Expand each in its last column.
        static constexpr int rows[5][4] = {
            {0,1,2,3}, {0,1,2,4}, {0,1,3,4}, {0,2,3,4}, {1,2,3,4}
        };
        for (const auto& r : rows) {
            auto [i,j,k,l] = r;
            Wide determinant = Wide(w[l])*minors[i][j][k] - Wide(w[k])*minors[i][j][l]
                             + Wide(w[j])*minors[i][k][l] - Wide(w[i])*minors[j][k][l];
            if (determinant % p) return false;
        }
        return true;
    }
};

Set lift(int D, const Set& old, int n, int N, std::vector<int> primes,
         Wide expected_tried, std::size_t expected_left) {
    if (N % n) throw std::runtime_error("Bad lift");
    std::vector<Place> places;
    for (int prime : primes) {
        places.emplace_back(D, prime);
        if (N % places.back().m) throw std::runtime_error("Incompatible period");
    }
    Set result;
    Wide tried = 0;
    for (const auto& r : old) {
        for (int a = r[0]; a < N; a += n) for (int b = r[1]; b < N; b += n) {
            if (r[0] == r[1] && a > b) continue;
            for (int c = r[2]; c < N; c += n) {
                if (r[1] == r[2] && b > c) continue;
                for (auto& place : places) place.first_three(a,b,c);
                for (int d = r[3]; d < N; d += n) {
                    if (r[2] == r[3] && c > d) continue;
                    ++tried;
                    if (std::all_of(places.begin(), places.end(),
                                    [d](Place& place){return place.dependent(d);})) {
                        Quadruple q{a,b,c,d};
                        std::sort(q.begin(),q.end());
                        result.push_back(q);
                    }
                }
            }
        }
    }
    std::sort(result.begin(),result.end());
    if (std::adjacent_find(result.begin(),result.end()) != result.end())
        throw std::runtime_error("Duplicate lift");
    std::cout << D << "  " << n << "  " << N << "  " << tried << "  " << result.size() << std::endl;
    if (tried != expected_tried || result.size() != expected_left)
        throw std::runtime_error("Count mismatch");
    return result;
}

int main() {
    const Set initial = {{0,0,0,0}};
    std::cout << "|Delta|  old_modulus  new_modulus  tested  remaining\n";
    Set a = lift(87, initial, 1, 102, {103}, 4780230, 13125);
    a = lift(87, a, 102, 1530, {1531}, 653917425, 625);
    a = lift(87, a, 1530, 7650, {151}, 390625, 915);
    std::set<Quadruple> projection;
    for (auto q : a) {
        for (int& x : q) x %= 18;
        std::sort(q.begin(),q.end());
        projection.insert(q);
    }
    if (projection.size() != 15) throw std::runtime_error("Unexpected projection");
    std::cout << "87 projects to 15 quadruples modulo 18\n";
    Set b(projection.begin(),projection.end());
    lift(87,b,18,486,{487,1459},7971615,0);
    lift(348,initial,1,486,{487,1459},2353329126LL,0);
    a = lift(432,initial,1,36,{109},82251,106);
    lift(432,a,36,144,{433},26212,0);
    a = lift(675,initial,1,40,{241},123410,1);
    lift(675,a,40,280,{13},2401,0);
}
