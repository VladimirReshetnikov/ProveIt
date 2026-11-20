// GCC or Clang in C++17 mode, with signed 128-bit integer support.
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <vector>

#include "shadow_lp.hpp"
#include "witness.hpp"

using Int = long long;
using Wide = __int128_t;
using Center = std::array<Int, 3>;

// Lengths in millionths, twice-area in trillionths.
constexpr Int chord = 438920;
constexpr Int inradius = 102000;
constexpr Int target = 116520000000LL;
constexpr int depth_limit = 16;

struct Counts {
    Int cells = 0;
    Int span = 0;
    Int polygon = 0;
    int max_depth = 0;
};

Int motion_error(Int m, const Center& center) {
    // The norm of any integer-scaled representative in the box is at
    // least sqrt(min_squared). Its floor is between m and 2*m inclusive.
    Int min_squared = m*m;
    for (Int component : center) {
        const Int nearest = std::max(0LL, std::abs(component) - 1);
        min_squared += nearest * nearest;
    }
    Int lo = m, hi = 2*m + 1;
    while (hi - lo > 1) {
        const Int mid = (lo + hi)/2;
        if (mid*mid <= min_squared) lo = mid;
        else hi = mid;
    }
    // 849000 > 2*sqrt(3)*245000.
    return (849000 + lo - 1)/lo;
}

bool certify(const Center& center, int depth, Counts& counts) {
    ++counts.cells;
    counts.max_depth = std::max(counts.max_depth, depth);
    const Int m = 1LL << depth;
    const auto [b,c,d] = center;
    const Int a = m;
    const Int norm_sq = a*a + b*b + c*c + d*d;
    const std::array<Int,3> xrow{a*a+b*b-c*c-d*d, 2*(b*c-a*d), 2*(b*d+a*c)};
    const std::array<Int,3> yrow{2*(b*c+a*d), a*a-b*b+c*c-d*d, 2*(c*d-a*b)};
    const Int error = motion_error(m, center);
    const Int denominator = 10*norm_sq;  // witness units 1e-7 to units 1e-6
    auto dot = [](const std::array<Int,3>& axis, const int (&p)[3]) {
        return axis[0]*p[0] + axis[1]*p[1] + axis[2]*p[2];
    };
    std::array<Int, std::size(witness)> y;
    for (std::size_t j = 0; j < y.size(); ++j)
        y[j] = dot(yrow, witness[j]);
    const auto [low,high] = std::minmax_element(y.begin(),y.end());
    if (Wide(chord)*(*high-*low) > Wide(target + 2*chord*error)*denominator) {
        ++counts.span;
        return true;
    }
    if (depth >= 4) {
        // Every rounded point belongs to the true shadow across this box.
        const Wide divisor = Wide(denominator)*(inradius+error);
        auto inward = [divisor](Int coord) {
            return Int(Wide(coord)*(inradius-2)/divisor);
        };
        std::vector<ShadowPt> points;
        points.reserve(y.size());
        for (std::size_t j = 0; j < y.size(); ++j)
            points.push_back({inward(dot(xrow,witness[j])), inward(y[j])});
        if (shadow_area_exceeds(points, chord, target)) {
            ++counts.polygon;
            return true;
        }
    }
    if (depth == depth_limit) return false;
    for (int mask = 0; mask < 8; ++mask) {
        Center child;
        for (int j = 0; j < 3; ++j)
            child[j] = 2*center[j] + ((mask & (1 << j)) ? 1 : -1);
        if (!certify(child, depth+1, counts)) return false;
    }
    return true;
}

int main() {
    Counts counts;
    const bool ok = certify({0,0,0}, 0, counts);
    std::cout << (ok ? "All rotations certified" : "Unresolved rotation cell")
              << ". Cells " << counts.cells << ", span exclusions " << counts.span
              << ", polygon exclusions " << counts.polygon
              << ", maximum depth " << counts.max_depth << ".\n";
    return ok ? 0 : 1;
}
