"""Exact longest common substrings of SLP words, with occurrence witnesses.

The cut-pair/periodic-extension framework follows Matsubara et al. (TCS 2009).
Our overlap construction uses dyadic prefix seeds and the existing AP matcher;
our equality backend has different costs from the paper's FM data structure.
All loops depend on grammar size or binary lengths, never expanded word length.
"""
from .compressed_match import MatchTable, _clip, _last, _shift
from .compressed_words import CompressedLimit
from .compressed_endpoint import endpoint_overlaps


def adjacent_pairs(arena, nodes):
    """Exact directed signed bigrams: each occurs at some reachable rule cut."""
    pairs = set()
    for node in nodes:
        arena.tick()
        rule = arena.rules[node]
        if rule[0] == 'c':
            pairs.add((arena.last[rule[1]], arena.first[rule[2]]))
    arena.stats['adjacency_rules'] = arena.stats.get('adjacency_rules', 0)+len(nodes)
    return pairs


class CommonSubstring:
    def __init__(self, arena):
        self.arena, self.cache, self.cache_cells = arena, {}, 0

    def suffix(self, x, y):
        return self.arena.lcp(self.arena.inverse(x), self.arena.inverse(y))

    def endpoint_overlaps(self, x, y):
        """Certified endpoint APs allow unbounded binary-sized long periods."""
        if min(self.arena.lengths[x], self.arena.lengths[y]) < 128:
            return None
        return endpoint_overlaps(self.arena, x, y)

    def periodic_overlaps(self, x, y):
        """Certify a period at most 32; None means use the complete fallback.

        Each grammar rule stores a bit mask of phases at which its whole word
        agrees with the proposed periodic sequence. A finite prefix proposes
        the period but never certifies the rest of either word.
        """
        a = self.arena
        if min(a.lengths[x], a.lengths[y]) < 128:
            return None
        a.stats['lcs_periodic_trials'] = a.stats.get('lcs_periodic_trials', 0)+1
        sample, pending = [], [a.slice(y, 0, 64)]
        while pending:
            a.tick()
            node = pending.pop()
            rule = a.rules[node]
            if rule[0] == 't':
                sample.append(rule[1])
            else:
                pending.extend((rule[2], rule[1]))
        for period in range(1, 33):
            a.tick(len(sample))
            if all(value == sample[i % period] for i, value in enumerate(sample)):
                break
        else:
            return None
        pattern = sample[:period]
        letter_masks = {}
        for phase, value in enumerate(pattern):
            a.tick()
            letter_masks[value] = letter_masks.get(value, 0) | (1 << phase)
        all_phases, masks = (1 << period)-1, {}
        nodes = a._reachable([x, y])
        for node in nodes:
            a.tick()
            rule = a.rules[node]
            if rule[0] == 't':
                mask = letter_masks.get(rule[1], 0)
            else:
                left, right = rule[1:]
                shift = a.lengths[left] % period
                moved = ((masks[right] >> shift) |
                         (masks[right] << (period-shift))) & all_phases
                mask = masks[left] & moved
            masks[node] = mask
        a.stats['lcs_periodic_rules'] = a.stats.get('lcs_periodic_rules', 0)+len(nodes)
        if not masks[x] or not (masks[y] & 1):
            return None
        # The least period of the 64-letter sample (at most 32) has a
        # primitive cyclic block. A full block matches only at phase zero.
        phase = (masks[x] & -masks[x]).bit_length()-1
        end_phase = (phase+a.lengths[x]) % period
        limit, result = min(a.lengths[x], a.lengths[y]), []
        for length in range(1, period):
            if length % period == end_phase:
                continue
            a.tick(length)
            if all(pattern[(end_phase-length+i) % period] == pattern[i]
                   for i in range(length)):
                result.append((length, 0, 1))
        first = end_phase or period
        count = (limit-first)//period+1
        if count:
            result.append((first, period if count > 1 else 0, count))
        a.stats['lcs_periodic_hits'] = a.stats.get('lcs_periodic_hits', 0)+1
        return result

    def sparse_overlaps(self, x, y):
        """Enumerate at most 64 endpoint-forced lengths, then check them exactly.

        A suffix/prefix match must end at last(x) in y and start at first(y)
        in x. Saturated signed-letter counts choose the rarer candidate set.
        None leaves dense endpoints to the complete occurrence-table matcher.
        """
        a = self.arena
        nx, ny = a.lengths[x], a.lengths[y]
        if min(nx, ny) < 128:
            return None
        a.stats['lcs_sparse_trials'] = a.stats.get('lcs_sparse_trials', 0)+1
        first, last, counts = a.first[y], a.last[x], {}
        nodes = a._reachable([x, y])
        for node in nodes:
            a.tick()
            rule = a.rules[node]
            if rule[0] == 't':
                counts[node] = int(rule[1] == first), int(rule[1] == last)
            else:
                left, right = counts[rule[1]], counts[rule[2]]
                counts[node] = min(65, left[0]+right[0]), min(65, left[1]+right[1])
        a.stats['lcs_sparse_rules'] = a.stats.get('lcs_sparse_rules', 0)+len(nodes)
        from_x = counts[x][0] < counts[y][1]
        root, column = (x, 0) if from_x else (y, 1)
        if counts[root][column] > 64:
            return None
        result, pending = [], [(root, 0)]
        while pending:
            a.tick()
            node, offset = pending.pop()
            if not counts[node][column]:
                continue
            rule = a.rules[node]
            if rule[0] == 't':
                length = nx-offset if from_x else offset+1
                if length > min(nx, ny):
                    continue
                a.stats['lcs_sparse_candidates'] = a.stats.get('lcs_sparse_candidates', 0)+1
                if a.equal(a.slice(x, nx-length, nx), a.slice(y, 0, length)):
                    result.append((length, 0, 1))
            else:
                left, right = rule[1:]
                pending.append((right, offset+a.lengths[left]))
                pending.append((left, offset))
        a.stats['lcs_sparse_hits'] = a.stats.get('lcs_sparse_hits', 0)+1
        return result

    def overlaps(self, x, y):
        """Disjoint APs of positive k with suffix_k(x) == prefix_k(y)."""
        a = self.arena
        a.tick()
        key = x, y
        if key in self.cache:
            return self.cache[key]
        nx, ny = a.lengths[x], a.lengths[y]
        limit, result = min(nx, ny), []
        # No overlap can extend outside this suffix and prefix. Keep cache
        # identity in the caller's roots while matching only the local words.
        if nx > limit:
            x = a.slice(x, nx-limit, nx)
            a.stats['lcs_trimmed_operands'] = a.stats.get('lcs_trimmed_operands', 0)+1
        if ny > limit:
            y = a.slice(y, 0, limit)
            a.stats['lcs_trimmed_operands'] = a.stats.get('lcs_trimmed_operands', 0)+1
        nx = ny = limit
        if limit and a.uniform[x] and a.uniform[y]:
            if a.uniform[x] == a.uniform[y]:
                result = [(1, 1 if limit > 1 else 0, limit)]
        elif (periodic := self.periodic_overlaps(x, y)) is not None:
            result = periodic
        elif (sparse := self.sparse_overlaps(x, y)) is not None:
            result = sparse
        elif (endpoint := self.endpoint_overlaps(x, y)) is not None:
            result = endpoint
        else:
            low = 1
            while low <= limit:
                a.tick()
                high = min(2*low-1, limit)
                seed = a.slice(y, 0, low)
                # Every candidate seed lies wholly in this suffix. Translate
                # its local start before applying the periodic extension test.
                window = a.slice(x, nx-high, nx)
                table = MatchTable(a, seed, window)
                a.stats['lcs_window_queries'] = a.stats.get('lcs_window_queries', 0)+1
                a.stats['lcs_window_bits'] = max(
                    a.stats.get('lcs_window_bits', 0), high.bit_length())
                for local in table.local(seed, window, 0, high):
                    ap = _shift(local, nx-high)
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
        self.cache[key] = result
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

    def shared_runs(self, nodes, common):
        """Maximum contiguous run using only the shared signed alphabet.

        Terminal ids encode signed letters uniquely within one arena. A letter
        outside common is a separator that no common substring can cross.
        """
        return self._runs(nodes, common, None, 'lcs_bound_nodes')

    def transition_runs(self, nodes, common, transitions):
        return self._runs(nodes, common, transitions, 'lcs_transition_bound_nodes')

    def _runs(self, nodes, common, transitions, counter):
        a, prefix, suffix, longest = self.arena, {}, {}, {}
        for node in nodes:
            a.tick()
            rule = a.rules[node]
            if rule[0] == 't':
                prefix[node] = suffix[node] = longest[node] = int(node in common)
            else:
                left, right = rule[1:]
                join = transitions is None or (a.last[left], a.first[right]) in transitions
                prefix[node] = prefix[left]+prefix[right] if join and prefix[left] == a.lengths[left] else prefix[left]
                suffix[node] = suffix[right]+suffix[left] if join and suffix[right] == a.lengths[right] else suffix[right]
                longest[node] = max(longest[left], longest[right], suffix[left]+prefix[right] if join else 0)
        a.stats[counter] = a.stats.get(counter, 0)+len(nodes)
        return longest

    def extensions(self, u, v):
        """Yield witnesses as soon as checked, so proved bounds can stop work."""
        a = self.arena
        yield self.extension(u, v, 0)
        for left, right, swapped in ((u, v, False), (v, u, True)):
            for ap in self.overlaps(a.rules[left][1], a.rules[right][2]):
                for k in self.critical(left, right, ap):
                    length, first, second = self.extension(left, right, k)
                    yield (length, second, first) if swapped else (length, first, second)

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
        xt = {n for n in xn if a.rules[n][0] == 't'}
        yt = {n for n in yn if a.rules[n][0] == 't'}
        common = xt & yt
        if not common:
            return 0, 0, 0
        xb = self.shared_runs(xn, common) if common != xt else a.lengths
        yb = self.shared_runs(yn, common) if common != yt else a.lengths
        limit = min(limit, xb[x], yb[y])
        if not best[0]:
            terminal = min(common)
            best = 1, xp[terminal], yp[terminal]
        if best[0] == limit:
            a.stats['lcs_bound_stops'] = a.stats.get('lcs_bound_stops', 0)+1
            return best
        xe, ye = adjacent_pairs(a, xn), adjacent_pairs(a, yn)
        transitions = xe & ye
        if transitions != xe:
            xb = self.transition_runs(xn, common, transitions)
        if transitions != ye:
            yb = self.transition_runs(yn, common, transitions)
        limit = min(limit, xb[x], yb[y])
        if best[0] == limit:
            a.stats['lcs_transition_stops'] = a.stats.get('lcs_transition_stops', 0)+1
            return best
        xs = sorted((n for n in xn if a.rules[n][0] == 'c'), key=lambda n: -xb[n])
        ys = sorted((n for n in yn if a.rules[n][0] == 'c'), key=lambda n: -yb[n])
        for u in xs:
            if xb[u] <= best[0]:
                break
            for v in ys:
                a.tick()
                if yb[v] <= best[0]:
                    break
                a.stats['lcs_cut_pairs'] = a.stats.get('lcs_cut_pairs', 0)+1
                pair_limit = min(xb[u], yb[v], limit)
                for length, first, second in self.extensions(u, v):
                    if length > best[0]:
                        best = min(length, limit), xp[u]+first, yp[v]+second
                        if best[0] == limit:
                            return best
                    if best[0] >= pair_limit:
                        a.stats['lcs_pair_stops'] = a.stats.get('lcs_pair_stops', 0)+1
                        break
        return best


def longest_common_substring(arena, x, y, cap=None):
    return CommonSubstring(arena).longest(x, y, cap)
