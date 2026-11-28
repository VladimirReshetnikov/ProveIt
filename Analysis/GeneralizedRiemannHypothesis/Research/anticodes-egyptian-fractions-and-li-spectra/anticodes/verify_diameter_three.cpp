// Independent checker for the 24 weighted inequalities in ambient dimension 15.
// Build: c++ -O3 -std=c++17 -march=native verify_diameter_three.cpp -o verify
// Run complete verification: ./verify   (optional: ./verify 22 for base-15 profile 22)
// The program enumerates disjoint signed multisets of size at most three,
// uses Hamming distances on their unary encodings, and seeks any overweight
// clique by a certified partial covering with weighted independent sets.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::uint64_t;
using Set = std::vector<Word>;
constexpr int upper_dimension = 15;
int dimension = upper_dimension;

struct SignedMultiset {
    Word plus, minus;
};

int pop(Word bits) { return __builtin_popcountll(bits); }

int distance(SignedMultiset a, SignedMultiset b) {
    return pop(a.plus ^ b.plus) + pop(a.minus ^ b.minus);
}

struct Multiset {
    Word entries;
    Word axes;
};

// Three unary levels per coordinate give the exact multiset metric.
void extend(std::vector<Multiset>& output, int remaining, int start,
            std::array<int, upper_dimension>& occupancy, Multiset current) {
    if (remaining == 0) {
        output.push_back(current);
        return;
    }
    for (int x = start; x < dimension; ++x) {
        Multiset next = current;
        next.entries |= Word(1) << (3*x + occupancy[x]);
        next.axes |= Word(1) << x;
        ++occupancy[x];
        extend(output, remaining-1, x, occupancy, next);
        --occupancy[x];
    }
}

int choose(int n, int k) {
    if (k < 0 || k > n) return 0;
    int ans = 1;
    for (int i=1; i<=k; ++i) ans = ans * (n-i+1) / i;
    return ans;
}

int model(int n) { return n + n*choose(n,2); }

struct Vertex {
    SignedMultiset x;
    int free_support;
};

std::vector<Vertex> enumerate_lens(const std::vector<int>& positive,
                                   const std::vector<int>& negative) {
    SignedMultiset anchor{0,0};
    int used_axes = 0;
    for (int multiplicity : positive) {
        anchor.plus |= ((Word(1)<<multiplicity)-1) << (3*used_axes++);
    }
    for (int multiplicity : negative) {
        anchor.minus |= ((Word(1)<<multiplicity)-1) << (3*used_axes++);
    }
    std::vector<Vertex> lens;
    for (int mass=1; mass<=3; ++mass) {
        std::array<int,upper_dimension> occupancy{};
        std::vector<Multiset> lists;
        extend(lists,mass,0,occupancy,{0,0});
        for (auto u : lists) for (auto v : lists) {
            if (u.axes & v.axes) continue;
            SignedMultiset z{u.entries,v.entries};
            int d = distance(anchor,z);
            if (d > 0 && d <= 6) {
                int outside = pop((u.axes | v.axes) >> used_axes);
                if (outside>3) throw std::logic_error("bad free support");
                lens.push_back({z,outside});
            }
        }
    }
    return lens; // Both anchors are omitted by construction.
}

void remove_bit(Set& set, int v) { set[v/64] &= ~(Word(1) << (v%64)); }
void add_bit(Set& set, int v) { set[v/64] |= Word(1) << (v%64); }

int first(const Set& set, int word = 0) {
    for (; word<int(set.size()); ++word)
        if (set[word]) return 64*word + __builtin_ctzll(set[word]);
    return -1;
}

struct CliqueSearch {
    std::vector<Set> neighbors;
    std::vector<int> weight;
    long long calls=0;
    std::vector<Word> center_labels;
    std::vector<Set> covered;

    bool exceeds(Set allowed, int target, Word live_centers = 0) {
        ++calls;
        // In the equality search, an active center covering all remaining
        // choices already covers every possible completed clique at this node.
        for (Word c=live_centers; c; c &= c-1) {
            int id=__builtin_ctzll(c);
            bool all_inside=true;
            for (size_t i=0;i<allowed.size();++i) {
                if (allowed[i] & ~covered[id][i]) { all_inside=false; break; }
            }
            if (all_inside) return false;
        }
        // earned = weight charged to every clique by the independent-set cover.
        int earned=0;
        std::vector<int> surplus=weight;
        Set active=allowed;
        std::vector<int> group;
        while (earned+1 < target) {
            int v=first(active);
            if (v<0) return false;
            group.clear();
            int fee=target;
            Set compatible=active;
            while (v>=0) {
                group.push_back(v);
                fee=std::min(fee,surplus[v]);
                remove_bit(compatible,v);
                for (int w=v/64; w<int(compatible.size()); ++w) {
                    compatible[w] &= ~neighbors[v][w];
                }
                v=first(compatible,v/64);
            }
            if (earned+fee >= target) break;
            for (int y: group) {
                surplus[y] -= fee;
                if (!surplus[y]) remove_bit(active,y);
            }
            earned += fee;
        }
        // Each clique collects at most 'earned' from all covered weight.
        // An overweight clique therefore intersects 'active'. Branch by its
        // first such vertex; retain all fully covered allowed vertices.
        int v=first(active);
        while (v>=0) {
            remove_bit(allowed,v);
            Word remaining_centers=live_centers;
            if (!center_labels.empty()) remaining_centers &= center_labels[v];
            if (weight[v]>=target) {
                if (!remaining_centers) return true;
                // The separately proved upper bound forbids extending this
                // equality-size clique; it already belongs to a balanced ball.
                remove_bit(active,v);
                v=first(active,v/64);
                continue;
            }
            Set keep(allowed.size());
            for (size_t i=0; i<allowed.size(); ++i) {
                keep[i]=allowed[i] & neighbors[v][i];
            }
            if (exceeds(std::move(keep),target-weight[v],remaining_centers)) return true;
            remove_bit(active,v);
            v=first(active,v/64);
        }
        return false;
    }
};

void certify(const std::vector<Vertex>& lens, int used, int order, const std::string& profile, SignedMultiset anchor) {
    std::array<int,4> numerators{},denominators{},weights{};
    int denominator=1;
    for (int k=0; k<4; ++k) {
        int a=choose(dimension-used,k-order), b=choose(dimension-used,k);
        if (b==0) { numerators[k]=0; denominators[k]=1; continue; }
        int g=std::gcd(a,b);
        numerators[k]=a/g; denominators[k]=b/g;
        denominator=std::lcm(denominator,denominators[k]);
    }
    for (int k=0; k<4; ++k) weights[k]=numerators[k]*(denominator/denominators[k]);
    std::vector<Vertex> candidates;
    for (auto z:lens) if (weights[z.free_support]) candidates.push_back(z);

    // Reorder by decreasing induced degree, then by a deterministic multiset
    // order unrelated to the primary checker's recursive coordinate sequence.
    int nv=candidates.size();
    std::vector<int> degree(nv),perm(nv);
    for (int i=0;i<nv;++i) for (int j=0;j<i;++j) {
        if (distance(candidates[i].x,candidates[j].x)<=6) {
            ++degree[i]; ++degree[j];
        }
    }
    std::iota(perm.begin(),perm.end(),0);
    std::stable_sort(perm.begin(),perm.end(),[&](int a,int b) {
        if (degree[a]!=degree[b]) return degree[a]>degree[b];
        if (weights[candidates[a].free_support]!=weights[candidates[b].free_support])
            return weights[candidates[a].free_support]>weights[candidates[b].free_support];
        return a<b;
    });
    std::vector<Vertex> sorted;
    for (int i:perm) sorted.push_back(candidates[i]);
    CliqueSearch search;
    int words=(nv+63)/64;
    search.neighbors.assign(nv,Set(words));
    for (int i=0;i<nv;++i) {
        search.weight.push_back(weights[sorted[i].free_support]);
        for (int j=0;j<i;++j) if (distance(sorted[i].x,sorted[j].x)<=6) {
            add_bit(search.neighbors[i],j); add_bit(search.neighbors[j],i);
        }
    }
    int difference=0;
    for (int i=0; i<=order; ++i) difference+=
        ((order-i)%2 ? -1 : 1)*choose(order,i)*model(dimension+i);
    int inclusive_bound=denominator*(difference-(order==0 ? 2 : 0));
    Set all(words,~Word(0));
    if(nv%64) all.back()=(Word(1)<<(nv%64))-1;
    std::cout << "N=" << dimension << " profile=" << profile << " j=" << order << " vertices=" << nv
              << " scale=" << denominator << " bound=" << inclusive_bound << std::flush;
    bool failure=search.exceeds(all,inclusive_bound+1);
    std::cout << " nodes=" << search.calls << (failure ? " FAIL" : " PASS") << std::endl;
    if (failure) throw std::runtime_error("an overweight clique exists");
    if(order) return;

    // Enumerate possible balanced midpoints by signed submultisets with
    // three tokens of the six anchor tokens. Unary levels must form prefixes.
    std::vector<SignedMultiset> centers;
    auto prefix_ok = [](Word w) {
        for (int i=0;i<dimension;++i) {
            Word field=(w>>(3*i))&7;
            if (field & (field+1)) return false;
        }
        return true;
    };
    for (Word pos=anchor.plus;;pos=(pos-1)&anchor.plus) {
        for (Word neg=anchor.minus;;neg=(neg-1)&anchor.minus) {
            if(pop(pos)+pop(neg)==3 && std::abs(pop(pos)-pop(neg))==1
               && prefix_ok(pos) && prefix_ok(neg)) centers.push_back({pos,neg});
            if(!neg) break;
        }
        if(!pos) break;
    }
    if(centers.size()>=64) throw std::logic_error("center mask overflow");
    search.covered.assign(centers.size(),Set(words));
    search.center_labels.assign(nv,0);
    for(size_t id=0;id<centers.size();++id) for(int v=0;v<nv;++v) {
        if(distance(sorted[v].x,centers[id])<=3) {
            search.center_labels[v] |= Word(1)<<id;
            add_bit(search.covered[id],v);
        }
    }
    search.calls=0;
    Word live=(Word(1)<<centers.size())-1;
    failure=search.exceeds(all,inclusive_bound,live);
    std::cout << "N=" << dimension << " profile=" << profile << " equality"
              << " centers=" << centers.size() << " nodes=" << search.calls
              << (failure ? " FAIL" : " PASS") << std::endl;
    if(failure) throw std::runtime_error("uncovered equality clique");
}

int main(int argc,char** argv) {
    const std::vector<std::vector<int>> parts={{3},{2,1},{1,1,1}};
    std::string only=argc==2 ? argv[1] : "";
    int profiles=0;
    for (dimension=(only.empty()?2:15); dimension<=upper_dimension; ++dimension) {
        for (int i=0;i<3;++i) for(int j=i;j<3;++j) {
            std::string profile=std::to_string(i)+std::to_string(j);
            if(!only.empty() && profile!=only) continue;
            int used=static_cast<int>(parts[i].size()+parts[j].size());
            if(used>dimension) continue;
            ++profiles;
            std::vector<Vertex> lens=enumerate_lens(parts[i],parts[j]);
            SignedMultiset anchor{0,0};
            int a=0;
            for(int x:parts[i]) anchor.plus |= ((Word(1)<<x)-1)<<(3*a++);
            for(int x:parts[j]) anchor.minus |= ((Word(1)<<x)-1)<<(3*a++);
            for(int order=(dimension==15?3:0);order>=0;--order)
                certify(lens,used,order,profile,anchor);
        }
    }
    return profiles ? EXIT_SUCCESS : EXIT_FAILURE;
}
