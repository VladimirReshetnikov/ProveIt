#pragma once

#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Column = std::array<int, 5>;
using Wide = std::int64_t;

struct ColumnTable {
    int period;
    int prime;
    // columns[residue][order] is x^residue D^order with its constant coordinate removed.
    std::vector<std::array<Column, 5>> columns;
    std::vector<int> inverse;

    explicit ColumnTable(const std::string& path) {
        std::ifstream input(path);
        if (!(input >> period >> prime) || period < 1 || prime < 2)
            throw std::runtime_error("Invalid column table: " + path);

        columns.resize(period);
        for (auto& residue : columns)
            for (auto& column : residue)
                for (int& entry : column)
                    if (!(input >> entry) || entry < 0 || entry >= prime)
                        throw std::runtime_error("Invalid column entry: " + path);

        inverse.resize(prime);
        inverse[1] = 1;
        for (int k = 2; k < prime; ++k)
            inverse[k] = prime - int(Wide(prime / k) * inverse[prime % k] % prime);
    }
};

// Fix the first two columns after the distinguished column 1 has been removed.
// If independent, they leave a three-dimensional quotient. Two more columns make
// a dependent quadruple exactly when one quotient vector is zero or their lines agree.
class ColumnQuotient {
    const ColumnTable& table;
    bool rank_below_two = true;
    int pivot_row_one = 0;
    int pivot_row_two = 0;
    std::array<int, 3> free_rows{};
    std::array<std::array<int, 3>, 3> minor_coefficients{};

public:
    ColumnQuotient(const ColumnTable& source, int first, int second) : table(source) {
        const Column& x = table.columns[first][first == 0];
        const Column& y = table.columns[second][(second == 0) + (second == first)];
        const int p = table.prime;

        for (int i = 0; i < 5; ++i) {
            for (int j = i + 1; j < 5; ++j) {
                const int pivot_minor = int((Wide(x[i])*y[j] - Wide(x[j])*y[i]) % p);
                if (pivot_minor == 0) continue;
                rank_below_two = false;
                pivot_row_one = i;
                pivot_row_two = j;

                // For each remaining row k, record the cofactor expansion of
                // det([x,y,z] on rows i,j,k), as a linear form in z[k], z[i], z[j].
                int coordinate = 0;
                for (int k = 0; k < 5; ++k) {
                    if (k == i || k == j) continue;
                    free_rows[coordinate] = k;
                    minor_coefficients[coordinate] = {
                        pivot_minor,
                        int((Wide(y[k])*x[j] - Wide(x[k])*y[j]) % p),
                        int((Wide(x[k])*y[i] - Wide(y[k])*x[i]) % p)
                    };
                    ++coordinate;
                }
                return;
            }
        }
    }

    int projective_key(const Column& column) const {
        // When the initial pair is dependent, every completion is dependent.
        if (rank_below_two) return 0;
        const int p = table.prime;
        int normalization = 0;
        std::array<int, 3> image{};
        for (int k = 0; k < 3; ++k) {
            const auto& c = minor_coefficients[k];
            const Wide sum = Wide(c[0])*column[free_rows[k]]
                           + Wide(c[1])*column[pivot_row_one]
                           + Wide(c[2])*column[pivot_row_two];
            image[k] = int(sum % p);
            if (image[k] < 0) image[k] += p;
            if (normalization == 0 && image[k] != 0)
                normalization = table.inverse[image[k]];
        }
        if (normalization == 0) return 0;
        for (int& value : image) value = int(Wide(value)*normalization % p);

        // Give disjoint ranges to [1:b:c], [0:1:c], and [0:0:1]. Zero is reserved.
        if (image[0] != 0) return 1 + image[1]*p + image[2];
        if (image[1] != 0) return 1 + p*p + image[2];
        return 1 + p*p + p;
    }
};

inline bool dependent_keys(int first, int second) {
    return first == 0 || second == 0 || first == second;
}
