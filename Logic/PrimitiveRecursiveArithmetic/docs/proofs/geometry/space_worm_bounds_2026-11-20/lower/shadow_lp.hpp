#ifndef SPACE_WORM_SHADOW_LP_HPP
#define SPACE_WORM_SHADOW_LP_HPP

#include <algorithm>
#include <cstdint>
#include <vector>

struct ShadowPt {
    long long x;
    long long y;
};

namespace shadow_detail {
using Wide = __int128_t;

// Signed turn in coordinates (height, horizontal coordinate).
inline long long turn(ShadowPt a, ShadowPt b, ShadowPt c) {
    return (b.y-a.y)*(c.x-a.x)-(b.x-a.x)*(c.y-a.y);
}

inline void chain_append(std::vector<ShadowPt>& chain, ShadowPt p, bool upper) {
    while (chain.size() >= 2) {
        const auto n = chain.size();
        const auto bend = turn(chain[n-2],chain[n-1],p);
        if (upper ? bend<0 : bend>0) break;
        chain.pop_back();
    }
    chain.push_back(p);
}

struct Ratio {
    long long num;
    long long den;  // strictly positive
};

// Heights range from the first to the last chain vertex. The cursor
// persists over calls made in increasing height order.
inline Ratio x_at(const std::vector<ShadowPt>& chain, std::size_t& cursor, long long y) {
    while (cursor+2 < chain.size() && chain[cursor+1].y < y) ++cursor;
    const auto a=chain[cursor], b=chain[cursor+1];
    const auto den=b.y-a.y;
    return {a.x*(b.y-y)+b.x*(y-a.y),den};
}

struct Hinge {
    long long a;
    long long b;  // max(0,a+b*c)
};

struct Corner {
    Ratio where;
    long long weight;
};

inline bool ratio_less(const Corner& a,const Corner& b) {
    return Wide(a.where.num)*b.where.den < Wide(b.where.num)*a.where.den;
}
}  // namespace shadow_detail

// For coordinates of absolute value <= 300000 and 0 <= d <= 1000000.
// Returns true only if every convex planar set containing the input points
// and some horizontal segment of length d has twice-area > twice_area_target.
// No floating-point operations. Input can be unordered.
inline bool shadow_area_exceeds(const std::vector<ShadowPt>& input,
                                long long d, long long twice_area_target) {
    using namespace shadow_detail;
    if (twice_area_target<0) return true;
    if (input.size()<3 || d<0) return false;
    auto pts=input;
    std::sort(pts.begin(),pts.end(),[](auto a,auto b) {
        return a.y < b.y || (a.y==b.y && a.x < b.x);
    });
    std::vector<ShadowPt> left, right, half;
    std::vector<long long> heights;
    for (std::size_t i=0; i<pts.size();) {
        auto j=i+1;
        while (j<pts.size() && pts[j].y==pts[i].y) ++j;
        chain_append(left,pts[i],false);
        chain_append(right,pts[j-1],true);
        heights.push_back(pts[i].y);
        i=j;
    }
    if (heights.size()<2) return false;
    std::size_t li=0,ri=0;
    for (const auto y:heights) {
        const auto l=x_at(left,li,y), r=x_at(right,ri,y);
        const auto width_num=Wide(r.num)*l.den-Wide(l.num)*r.den;
        const auto half_floor=static_cast<long long>(width_num/(Wide(2)*l.den*r.den));
        chain_append(half,{half_floor,y},true);
    }
    // Build the CCW polygon of symmetric integer slice endpoints.
    std::vector<ShadowPt> ring=half;
    for (auto it=half.rbegin(); it!=half.rend(); ++it)
        if (it->x!=0 || (it!=half.rbegin() && it+1!=half.rend()))
            ring.push_back({-it->x,it->y});
    if (ring.size()<3) return false;
    std::vector<Hinge> hinges;
    std::vector<Corner> breaks;
    long long twice_base=0, to_median=0;
    for (std::size_t i=0; i<ring.size(); ++i) {
        const auto p=ring[i], q=ring[(i+1)%ring.size()];
        const auto nx=q.y-p.y, ny=p.x-q.x;
        const auto off=nx*p.x+ny*p.y;
        twice_base+=off;
        const auto a=d*(nx<0 ? -nx:nx)-2*off, b=2*ny;
        hinges.push_back({a,b});
        if (b<0) {
            to_median-=b;
            breaks.push_back({{a,-b},-b});
        } else if (b>0) {
            breaks.push_back({{-a,b},b});
        }
    }
    if (twice_base>twice_area_target) return true;
    if (twice_base<=0 || breaks.empty()) return false;
    std::sort(breaks.begin(),breaks.end(),ratio_less);
    Ratio minimizing=breaks.back().where;
    for (const auto& r:breaks) {
        to_median-=r.weight;
        if (to_median<=0) {
            minimizing=r.where;
            break;
        }
    }
    // The sum is twice the mixed-area increment. Compare after clearing
    // the positive denominator of the minimizing height.
    Wide bound=Wide(2)*(twice_base-twice_area_target)*minimizing.den;
    for (const auto h:hinges) {
        auto v=Wide(h.a)*minimizing.den+Wide(h.b)*minimizing.num;
        if (v>0) bound+=v;
    }
    return bound>0;
}
#endif
