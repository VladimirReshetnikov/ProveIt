"""Exact longest common substrings of SLP words, with occurrence witnesses.

The cut-pair/periodic-extension framework follows Matsubara et al. (TCS 2009).
Our overlap construction uses dyadic prefix seeds and the existing AP matcher;
our equality backend has different costs from the paper's FM data structure.
All loops depend on grammar size or binary lengths, never expanded word length.
"""
from .compressed_match import MatchTable, _clip, _last
from .compressed_words import CompressedLimit


class CommonSubstring:
    def __init__(self, arena):
        self.arena, self.cache, self.cache_cells = arena, {}, 0

    def suffix(self, x, y):
        return self.arena.lcp(self.arena.inverse(x), self.arena.inverse(y))

    def overlaps(self, x, y):
        """Disjoint APs of positive k with suffix_k(x) == prefix_k(y)."""
        a = self.arena
        a.tick()
        if (x, y) in self.cache:
            return self.cache[x, y]
        nx, ny = a.lengths[x], a.lengths[y]
        limit, result = min(nx, ny), []
        if limit and a.uniform[x] and a.uniform[y]:
            if a.uniform[x] == a.uniform[y]:
                result = [(1, 1 if limit > 1 else 0, limit)]
        else:
            low = 1
            while low <= limit:
                a.tick()
                high = min(2*low-1, limit)
                seed = a.slice(y, 0, low)
                table = MatchTable(a, seed, x)
                for ap in table.local(seed, x, nx-high, nx):
                    a.tick()
                    start, step, count = ap
                    if count == 1:
                        if a.lcp(a.slice(x, start, nx), y) >= nx-start:
                            result.append((nx-start, 0, 1))
                        continue
                    # All starts occupy a span shorter than the seed. Their
                    # common step is therefore a period of the seed and run.
                    xend = start+step+a.lcp(a.slice(x, start, nx), a.slice(x, start+step, nx))
                    yend = step+a.lcp(y, a.slice(y, step, ny))
                    if xend == nx:
                        good = _clip(ap, nx-yend, nx-low)
                        if good is not None:
                            result.append((nx-_last(good), good[1], good[2]))
                    else:
                        # Only coincident departures from the common periodic
                        # word can continue through x's nonperiodic tail.
                        special = xend-yend
                        if (_clip(ap, special, special) is not None
                                and a.lcp(a.slice(x, special, nx), y) >= nx-special):
                            result.append((nx-special, 0, 1))
                low *= 2
        if self.cache_cells+len(result)+1 > a.max_nodes:
            raise CompressedLimit('compressed-LCS overlap cache allowance exhausted')
        self.cache[x, y] = result
        self.cache_cells += len(result)+1
        a.stats['lcs_overlap_aps'] = a.stats.get('lcs_overlap_aps', 0)+len(result)
        return result

    def extension(self, x, y, k):
        """Extend a checked overlap of x's left child and y's right child."""
        a = self.arena
        _, left, right = a.rules[x]
        _, other_left, other_right = a.rules[y]
        cut, other_cut = a.lengths[left], a.lengths[other_left]
        before = self.suffix(a.slice(left, 0, cut-k), other_left)
        after = a.lcp(right, a.slice(other_right, k, a.lengths[other_right]))
        a.stats['lcs_extensions'] = a.stats.get('lcs_extensions', 0)+1
        return k+before+after, cut-k-before, other_cut-before

    def critical(self, x, y, ap):
        """At most six AP members suffice to maximize the extension length."""
        a = self.arena
        start, step, count = ap
        if count == 1:
            return [start]
        _, left, right = a.rules[x]
        _, other_left, other_right = a.rules[y]
        ll, rr = a.lengths[left], a.lengths[right]
        ol, ore = a.lengths[other_left], a.lengths[other_right]
        tail = a.slice(left, ll-step, ll)
        head = a.slice(other_right, 0, step)
        e1 = a.lcp(right, a.power(tail, (rr+step-1)//step))
        e2 = step+self.suffix(a.slice(left, 0, ll-step), a.slice(left, step, ll))
        e3 = step+a.lcp(other_right, a.slice(other_right, step, ore))
        e4 = self.suffix(other_left, a.power(head, (ol+step-1)//step))
        indices = {0, count-1}
        for threshold in (e2-e4, e3-e1):
            q = (threshold-start)//step
            indices.update((max(0, min(count-1, q)), max(0, min(count-1, q+1))))
        a.tick(len(indices))
        return [start+i*step for i in sorted(indices)]

    def offsets(self, root):
        a, positions = self.arena, {root: 0}
        nodes = a._reachable([root])
        for node in reversed(nodes):
            a.tick()
            rule = a.rules[node]
            if rule[0] == 'c':
                left, right = rule[1:]
                for child, offset in ((left, positions[node]), (right, positions[node]+a.lengths[left])):
                    positions[child] = min(positions.get(child, offset), offset)
        return nodes, positions

    def longest(self, x, y, cap=None):
        """Return (min(LCS length, cap), x start, y start); empty uses (0,0,0)."""
        a = self.arena
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError('common substring cap must be a nonnegative integer')
        limit = min(a.lengths[x], a.lengths[y])
        if cap is not None:
            limit = min(limit, cap)
        a.tick()
        if not limit:
            return 0, 0, 0
        prefix = a.lcp(x, y, limit)
        best = prefix, 0, 0
        if prefix == limit:
            return best
        xn, xp = self.offsets(x)
        yn, yp = self.offsets(y)
        terminals = set(n for n in xn if a.rules[n][0] == 't')
        common = next((n for n in yn if n in terminals), None)
        if common is None:
            return 0, 0, 0
        if not best[0]:
            best = 1, xp[common], yp[common]
        if best[0] == limit:
            return best
        xs = sorted((n for n in xn if a.rules[n][0] == 'c'), key=lambda n: -a.lengths[n])
        ys = sorted((n for n in yn if a.rules[n][0] == 'c'), key=lambda n: -a.lengths[n])
        for u in xs:
            if a.lengths[u] <= best[0]:
                break
            for v in ys:
                a.tick()
                if a.lengths[v] <= best[0]:
                    break
                a.stats['lcs_cut_pairs'] = a.stats.get('lcs_cut_pairs', 0)+1
                candidates = [(self.extension(u, v, 0), False)]
                for left, right, swapped in ((u, v, False), (v, u, True)):
                    for ap in self.overlaps(a.rules[left][1], a.rules[right][2]):
                        for k in self.critical(left, right, ap):
                            candidates.append((self.extension(left, right, k), swapped))
                for (length, first, second), swapped in candidates:
                    if length > best[0]:
                        if swapped:
                            first, second = second, first
                        best = min(length, limit), xp[u]+first, yp[v]+second
                        if best[0] == limit:
                            return best
        return best


def longest_common_substring(arena, x, y, cap=None):
    return CommonSubstring(arena).longest(x, y, cap)
