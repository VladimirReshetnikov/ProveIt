#include "quotient.hpp"

using Quadruple = std::array<int, 4>;

std::vector<Quadruple> read_quadruples(const std::string& path) {
    std::ifstream input(path);
    if (!input) throw std::runtime_error("Missing residue list: " + path);
    std::vector<Quadruple> rows;
    Quadruple row{};
    while (input >> row[0] >> row[1] >> row[2] >> row[3]) rows.push_back(row);
    if (!input.eof()) throw std::runtime_error("Malformed residue list: " + path);
    return rows;
}

// The main loop lifts the four positions in their old residue order. This
// may differ from their order modulo 18 or 30, so include every permutation.
std::vector<std::uint8_t> allowed_signatures(const std::string& path, int modulus) {
    std::vector<std::uint8_t> present(modulus*modulus*modulus*modulus);
    for (Quadruple row : read_quadruples(path)) {
        for (int& value : row) value %= modulus;
        std::sort(row.begin(), row.end());
        do {
            const int index = ((row[0]*modulus + row[1])*modulus + row[2])*modulus + row[3];
            present[index] = 1;
        } while (std::next_permutation(row.begin(), row.end()));
    }
    return present;
}

int main(int argc, char** argv) {
    if (argc != 5) return 2;
    constexpr int old_period = 102;
    const auto old_rows = read_quadruples(argv[1]);
    const auto allowed18 = allowed_signatures(argv[2], 18);
    const auto allowed30 = allowed_signatures(argv[3], 30);
    const ColumnTable table(argv[4]);
    if (table.period != 1530 || table.prime != 1531)
        throw std::runtime_error("Expected a period-1530 table at prime 1531");

    Wide total = 0, matched = 0, failures = 0;
    for (const Quadruple& row : old_rows) {
        for (int a = row[0]; a < table.period; a += old_period) {
            // Lifts of equal old residues may be sorted within their block.
            // Lifts of unequal old residues keep their original positions.
            const int first_b = row[1] == row[0] ? a : row[1];
            for (int b = first_b; b < table.period; b += old_period) {
                const ColumnQuotient quotient(table, a, b);
                const int prefix18 = (a%18)*18 + b%18;
                const int prefix30 = (a%30)*30 + b%30;

                const int first_c = row[2] == row[1] ? b : row[2];
                for (int c = first_c; c < table.period; c += old_period) {
                    // For a fixed a,b,c, one contiguous slice answers all d's.
                    const auto* match18 = &allowed18[(prefix18*18 + c%18)*18];
                    const auto* match30 = &allowed30[(prefix30*30 + c%30)*30];
                    const int order_c = (c == 0) + (c == a) + (c == b);
                    const int key_c = quotient.projective_key(table.columns[c][order_c]);

                    const int first_d = row[3] == row[2] ? c : row[3];
                    for (int d = first_d; d < table.period; d += old_period) {
                        ++total;
                        if (!match18[d%18] || !match30[d%30]) continue;
                        ++matched;
                        const int order_d = (d == 0) + (d == a) + (d == b) + (d == c);
                        const int key_d = quotient.projective_key(table.columns[d][order_d]);
                        if (dependent_keys(key_c, key_d)) {
                            ++failures;
                            std::cout << a << ' ' << b << ' ' << c << ' ' << d << '\n';
                        }
                    }
                }
            }
        }
    }
    std::cerr << "candidate lifts " << total << ", signature-compatible " << matched
              << ", surviving " << failures << '\n';
    return failures != 0;
}
