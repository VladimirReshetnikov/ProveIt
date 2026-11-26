// Exhaustively lift the four residues accompanying the normalized exponent zero.
// Input tables are produced by verify_last_quintic.py in the working directory.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Vector = std::array<int, 4>;
using Quadruple = std::array<int, 4>;
using Wide = std::int64_t;

struct Place {
    int period, prime;
    std::vector<std::array<Vector, 5>> columns;
    std::array<int, 5> residues{};
    Vector cofactor{};

    explicit Place(int p) {
        std::ifstream input("prime-" + std::to_string(p) + ".txt");
        if (!(input >> period >> prime) || prime != p || period < 1)
            throw std::runtime_error("Incorrect prime table");
        columns.resize(period);
        for (auto& group : columns)
            for (auto& v : group)
                for (auto& coordinate : v)
                    if (!(input >> coordinate) || coordinate < 0 || coordinate >= p)
                        throw std::runtime_error("Incorrect column data");
    }

    const Vector& column(int exponent, int position) {
        int residue = exponent % period;
        residues[position] = residue;
        int order = std::count(residues.begin(), residues.begin() + position, residue);
        return columns[residue][order];
    }

    // The same first three columns are reused for all lifts of the last exponent.
    void first_three(int a, int b, int c) {
        Vector x = column(a, 1), y = column(b, 2), z = column(c, 3);
        Wide minor[4][4]{};
        for (int i = 0; i < 4; ++i)
            for (int j = i + 1; j < 4; ++j)
                minor[i][j] = (Wide(x[i])*y[j] - Wide(x[j])*y[i]) % prime;
        for (int omit = 0; omit < 4; ++omit) {
            std::array<int, 3> rows{};
            int pos = 0;
            for (int row = 0; row < 4; ++row)
                if (row != omit) rows[pos++] = row;
            auto [i, j, k] = rows;
            Wide value = minor[i][j]*z[k] - minor[i][k]*z[j] + minor[j][k]*z[i];
            cofactor[omit] = ((omit % 2 == 1) ? value : -value) % prime;
        }
    }

    bool dependent(int d) {
        const Vector& v = column(d, 4);
        Wide determinant = 0;
        for (int i = 0; i < 4; ++i) determinant += Wide(cofactor[i])*v[i];
        return determinant % prime == 0;
    }
};

std::vector<Quadruple> lift(const std::vector<Quadruple>& old, int n, int N,
                            std::vector<int> primes, Wide expected_tried, int expected_left) {
    std::vector<Place> places;
    for (int p : primes) {
        places.emplace_back(p);
        if (N % places.back().period != 0) throw std::runtime_error("Incompatible period");
    }
    if (N % n != 0) throw std::runtime_error("Incompatible lift");
    std::vector<Quadruple> survivors;
    Wide tried = 0;
    for (auto r : old) {
        for (int a = r[0]; a < N; a += n) {
            for (int b = r[1]; b < N; b += n) {
                if (r[0] == r[1] && a > b) continue;
                for (int c = r[2]; c < N; c += n) {
                    if (r[1] == r[2] && b > c) continue;
                    for (auto& place : places) place.first_three(a, b, c);
                    for (int d = r[3]; d < N; d += n) {
                        if (r[2] == r[3] && c > d) continue;
                        ++tried;
                        bool survives = std::all_of(places.begin(), places.end(),
                            [d](Place& place) {return place.dependent(d);});
                        if (survives) {
                            Quadruple q{a,b,c,d};
                            std::sort(q.begin(), q.end());
                            survivors.push_back(q);
                        }
                    }
                }
            }
        }
    }
    std::sort(survivors.begin(), survivors.end());
    if (std::adjacent_find(survivors.begin(), survivors.end()) != survivors.end())
        throw std::runtime_error("Duplicate lift");
    std::cout << N << "  " << tried << "  " << survivors.size() << '\n';
    if (tried != expected_tried || int(survivors.size()) != expected_left)
        throw std::runtime_error("Count mismatch");
    return survivors;
}

int main() {
    std::vector<Quadruple> survivors = {{0,0,0,0}};
    std::cout << "modulus  inspected  surviving\n";
    survivors = lift(survivors, 1, 200, {601}, 68685050, 119264);
    survivors = lift(survivors, 200, 1400, {1051, 4201}, 279218674, 196);
    survivors = lift(survivors, 1400, 4200, {6301}, 15876, 5876);
    survivors = lift(survivors, 4200, 12600, {757}, 475956, 214120);
    survivors = lift(survivors, 12600, 25200, {337}, 3425920, 0);
}
