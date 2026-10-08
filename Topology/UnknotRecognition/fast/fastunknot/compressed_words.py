"""Exact straight-line-program words and compressed free-group reduction.

Equality uses a bounded exact DAG walk and indexed split/periodicity-compaction
assertions (Plandowski, as exposed in Schleimer, arXiv:math/0608563, Section 8).
No fingerprints or expanded-word allocations decide equality. Slicing and
boundary cancellation implement the compressed free-group reduction of the
same paper. Resource caps interrupt;
they never substitute a probabilistic or incomplete equality answer.
"""
from collections import defaultdict
from heapq import heappop, heappush
from math import gcd


class CompressedLimit(RuntimeError):
    pass


class WordArena:
    """Interned binary SLPs; node zero is empty, signed integers are letters.

    ``max_nodes`` also bounds live equality assertions and the equality cache.
    ``max_work`` charges cooperative abstract operations, not CPU instructions.
    ``equality_probe_steps`` caps a direct DAG walk before polynomial fallback;
    zero bypasses the probe. The default cap is independent of expanded length.
    ``prefix_probe_steps`` separately caps this walk for longest-prefix queries.
    All public word arguments are node ids obtained from this arena.
    """
    def __init__(self, *, max_nodes=100000, max_work=10000000, equality_probe_steps=64,
                 prefix_probe_steps=64,
                 check=lambda: None):
        for name, value in (('max_nodes', max_nodes), ('max_work', max_work),
                            ('equality_probe_steps', equality_probe_steps),
                            ('prefix_probe_steps', prefix_probe_steps)):
            if type(value) is not int or value < 0:
                raise ValueError(f'{name} must be a nonnegative integer')
        self.max_nodes, self.left, self.check = max_nodes, max_work, check
        self.equality_probe_steps = equality_probe_steps
        self.prefix_probe_steps = prefix_probe_steps
        self.rules, self.lengths, self.first, self.last = [None], [0], [0], [0]
        self._interned, self._inverse, self._reduced, self._equal_cache = {}, {0: 0}, {0: 0}, {}
        self.stats = dict(work=0, equality_calls=0, splits=0, compact_triples=0, peak_assertions=0,
                          probe_steps=0, probe_resolved=0, probe_fallbacks=0,
                          lcp_calls=0, lcp_probe_steps=0, lcp_probe_resolved=0, lcp_probe_fallbacks=0)

    def tick(self, amount=1):
        self.check()
        self.left -= amount
        self.stats['work'] += amount
        if self.left < 0:
            raise CompressedLimit('compressed-word work allowance exhausted')

    def _intern(self, rule, length, first, last):
        self.tick()
        known = self._interned.get(rule)
        if known is not None:
            return known
        if len(self.rules)-1 >= self.max_nodes:
            raise CompressedLimit('compressed-word node allowance exhausted')
        result = len(self.rules)
        self.rules.append(rule)
        self.lengths.append(length)
        self.first.append(first)
        self.last.append(last)
        self._interned[rule] = result
        return result

    def letter(self, value):
        if type(value) is not int or not value:
            raise ValueError('a free-group letter must be a nonzero integer')
        node = self._intern(('t', value), 1, value, value)
        self._reduced[node] = node
        return node

    def concat(self, left, right):
        self.tick()
        if not left:
            return right
        if not right:
            return left
        return self._intern(('c', left, right), self.lengths[left]+self.lengths[right],
                            self.first[left], self.last[right])

    def from_word(self, letters):
        nodes = [self.letter(x) for x in letters]
        while len(nodes) > 1:
            nodes = [self.concat(nodes[i], nodes[i+1]) if i+1 < len(nodes) else nodes[i]
                     for i in range(0, len(nodes), 2)]
        self.tick()
        return nodes[0] if nodes else 0

    def power(self, node, exponent):
        if type(exponent) is not int:
            raise ValueError('exponent must be an integer')
        if exponent < 0:
            node, exponent = self.inverse(node), -exponent
        result = 0
        while exponent:
            self.tick()
            if exponent & 1:
                result = self.concat(result, node)
            exponent >>= 1
            if exponent:
                node = self.concat(node, node)
        return result

    def _reachable(self, roots):
        seen, pending = set(), list(roots)
        while pending:
            self.tick()
            node = pending.pop()
            if not node or node in seen:
                continue
            seen.add(node)
            rule = self.rules[node]
            if rule[0] == 'c':
                pending.extend(rule[1:])
        # New nodes reference only earlier ids, giving a topological order.
        return sorted(seen)

    def inverse(self, node):
        if node in self._inverse:
            self.tick()
            return self._inverse[node]
        for current in self._reachable([node]):
            if current in self._inverse:
                continue
            rule = self.rules[current]
            if rule[0] == 't':
                result = self.letter(-rule[1])
            else:
                result = self.concat(self._inverse[rule[2]], self._inverse[rule[1]])
            self._inverse[current], self._inverse[result] = result, current
            if self._reduced.get(current) == current:
                self._reduced[result] = result
        return self._inverse[node]

    def slice(self, node, start, stop):
        """An exact half-open substring, constructing O(height) new SLP nodes."""
        if (type(start) is not int or type(stop) is not int
                or not 0 <= start <= stop <= self.lengths[node]):
            raise ValueError('invalid compressed substring bounds')
        pending, done = [(node, start, stop, False)], {}
        while pending:
            self.tick()
            current, lo, hi, ready = pending.pop()
            key = current, lo, hi
            if key in done:
                continue
            if lo == hi:
                done[key] = 0
            elif lo == 0 and hi == self.lengths[current]:
                done[key] = current
            else:
                _, a, b = self.rules[current]
                middle = self.lengths[a]
                parts = []
                if lo < middle:
                    parts.append((a, lo, min(hi, middle)))
                if hi > middle:
                    parts.append((b, max(0, lo-middle), hi-middle))
                if ready:
                    done[key] = (done[parts[0]] if len(parts) == 1
                                 else self.concat(done[parts[0]], done[parts[1]]))
                else:
                    pending.append((current, lo, hi, True))
                    pending.extend((*part, False) for part in parts if part not in done)
        result = done[node, start, stop]
        if self._reduced.get(node) == node:
            self._reduced[result] = result
        return result

    def _prefix_probe(self, a, b, cap, steps, counter):
        """Return (proved common-prefix length, resolved) by a bounded DAG walk.

        Skip identical subtrees; otherwise split the longer leading chunk.
        No expanded word is allocated. A fixed work cap prevents an unfolded
        traversal from inheriting the possibly exponential represented length.
        """
        left, right, matched = [a], [b], 0
        for _ in range(steps):
            self.tick()
            self.stats[counter] += 1
            u, v = left[-1], right[-1]
            if u == v:
                matched += self.lengths[u]
                if matched >= cap:
                    return cap, True
                left.pop()
                right.pop()
            elif self.first[u] != self.first[v]:
                return matched, True
            elif self.lengths[u] >= self.lengths[v]:
                _, x, y = self.rules[left.pop()]
                left.extend((y, x))
            else:
                _, x, y = self.rules[right.pop()]
                right.extend((y, x))
        return matched, False

    def _equality_probe(self, a, b):
        matched, resolved = self._prefix_probe(a, b, self.lengths[a],
                                              self.equality_probe_steps, 'probe_steps')
        return matched == self.lengths[a] if resolved else None

    def _remember_equal(self, key, result):
        if len(self._equal_cache) >= self.max_nodes:
            self._equal_cache.clear()
        self._equal_cache[key] = result
        self.tick()
        return result

    def equal(self, a, b):
        """Deterministic polynomial SLP equality; exhaustion raises, never guesses."""
        self.tick()
        self.stats['equality_calls'] += 1
        if a == b:
            return True
        if (self.lengths[a] != self.lengths[b] or self.first[a] != self.first[b]
                or self.last[a] != self.last[b]):
            return False
        key = min(a, b), max(a, b)
        if key in self._equal_cache:
            return self._equal_cache[key]
        if self.equality_probe_steps:
            result = self._equality_probe(a, b)
            if result is not None:
                self.stats['probe_resolved'] += 1
                return self._remember_equal(key, result)
            self.stats['probe_fallbacks'] += 1
        gamma, mentioned, overlaps = set(), defaultdict(set), defaultdict(set)
        pending, queued, dirty = [], set(), set()

        class Mismatch(Exception):
            pass

        def add(u, v, offset):
            self.tick()
            if offset == 0 and u[1] == v[1]:
                return
            # Represent a proper prefix inclusion as an overlap in reverse order.
            if offset == 0 and self.lengths[u[1]] > self.lengths[v[1]]:
                u, v = v, u
            if self.lengths[u[1]] == self.lengths[v[1]] == 1:
                if self.first[u[1]] != self.first[v[1]]:
                    raise Mismatch
                return
            assertion = u, v, offset
            if assertion in gamma:
                return
            gamma.add(assertion)
            if len(gamma) > self.max_nodes:
                raise CompressedLimit('compressed equality assertion allowance exhausted')
            self.stats['peak_assertions'] = max(self.stats['peak_assertions'], len(gamma))
            for node in (u, v):
                mentioned[node].add(assertion)
                if self.rules[node[1]][0] == 'c' and node not in queued:
                    heappush(pending, (-self.lengths[node[1]], -node[0], -node[1]))
                    queued.add(node)
            if self.lengths[u[1]] <= offset+self.lengths[v[1]]:
                overlaps[u, v].add(offset)
                dirty.add((u, v))

        def remove(assertion):
            self.tick()
            u, v, offset = assertion
            gamma.remove(assertion)
            for node in (u, v):
                mentioned[node].remove(assertion)
                if not mentioned[node]:
                    del mentioned[node]
            if self.lengths[u[1]] <= offset+self.lengths[v[1]]:
                overlaps[u, v].remove(offset)
                if not overlaps[u, v]:
                    del overlaps[u, v]

        try:
            add((0, a), (1, b), 0)
            while gamma:
                self.tick()
                _, neg_side, neg_index = heappop(pending)
                selected = -neg_side, -neg_index
                if selected not in mentioned:
                    continue  # An earlier exact shortcut discharged its assertions.
                side, index = selected
                _, aa, bb = self.rules[index]
                left, right, middle = (side, aa), (side, bb), self.lengths[aa]
                affected = list(mentioned[selected])
                # Remove the old conjunction first, so the allocation ceiling
                # applies to live assertions, not old and new copies together.
                for assertion in affected:
                    remove(assertion)
                for u, v, offset in affected:
                    if u == selected:
                        end = min(self.lengths[u[1]], offset+self.lengths[v[1]])
                        if offset < middle:
                            add(left, v, offset)
                        if end > middle:
                            if offset >= middle:
                                add(right, v, offset-middle)
                            else:
                                add(v, right, middle-offset)
                    elif v == selected:
                        add(u, left, offset)
                        if self.lengths[u[1]] > offset+middle:
                            add(u, right, offset+middle)
                # Unchanged pairs are already compact. Only additions can
                # introduce a new compactable triple; removals cannot do so.
                while dirty:
                    u, v = dirty.pop()
                    while True:
                        offsets = overlaps.get((u, v), ())
                        self.tick(len(offsets)+1)
                        values = sorted(offsets)
                        for k in range(len(values)-2):
                            self.tick()
                            i, j, last = values[k:k+3]
                            if j+last-i <= self.lengths[u[1]]:
                                remove((u, v, j))
                                remove((u, v, last))
                                add(u, v, i+gcd(j-i, last-i))
                                self.stats['compact_triples'] += 1
                                break
                        else:
                            break
                    dirty.discard((u, v))
                self.stats['splits'] += 1
            result = True
        except Mismatch:
            result = False
        return self._remember_equal(key, result)

    def lcp(self, a, b, cap=None):
        """Bounded direct walk, then exact bisection beyond the proved prefix."""
        self.stats['lcp_calls'] += 1
        hi = min(self.lengths[a], self.lengths[b])
        if cap is not None:
            if type(cap) is not int or cap < 0:
                raise ValueError('prefix cap must be a nonnegative integer')
            hi = min(hi, cap)
        if a == b:
            self.tick()
            return hi
        if not hi or self.first[a] != self.first[b]:
            self.tick()
            return 0
        lo = 0
        if self.prefix_probe_steps:
            lo, resolved = self._prefix_probe(a, b, hi, self.prefix_probe_steps, 'lcp_probe_steps')
            if resolved:
                self.stats['lcp_probe_resolved'] += 1
                return lo
            self.stats['lcp_probe_fallbacks'] += 1
        while lo < hi:
            self.tick()
            mid = (lo+hi+1)//2
            # The prefix before lo is already proved equal. Rechecking it
            # would duplicate work and can create needlessly large slices.
            if self.equal(self.slice(a, lo, mid), self.slice(b, lo, mid)):
                lo = mid
            else:
                hi = mid-1
        return lo

    def _multiply_reduced(self, a, b):
        if not a or not b or self.last[a] != -self.first[b]:
            result = self.concat(a, b)
        else:
            cancellation = self.lcp(self.inverse(a), b)
            result = self.concat(self.slice(a, 0, self.lengths[a]-cancellation),
                                 self.slice(b, cancellation, self.lengths[b]))
        self._reduced[result] = result
        return result

    def reduce(self, node):
        if node in self._reduced:
            self.tick()
            return self._reduced[node]
        for current in self._reachable([node]):
            if current not in self._reduced:
                _, a, b = self.rules[current]
                self._reduced[current] = self._multiply_reduced(self._reduced[a], self._reduced[b])
        return self._reduced[node]

    def cyclic_reduce(self, node):
        result = self.reduce(node)
        if result and self.first[result] == -self.last[result]:
            k = self.lcp(result, self.inverse(result), self.lengths[result]//2)
            result = self.slice(result, k, self.lengths[result]-k)
        self.tick()
        return result

    def substitute(self, roots, images):
        """Simultaneous letter substitution with shared free reduction."""
        mapped = {0: 0}
        for current in self._reachable(roots):
            rule = self.rules[current]
            if rule[0] == 't':
                mapped[current] = self.reduce(images.get(rule[1], current))
            else:
                mapped[current] = self._multiply_reduced(mapped[rule[1]], mapped[rule[2]])
        return [mapped[root] for root in roots]

    def occurrence(self, node, generator):
        """Absolute-letter count and first occurrence (position, signed letter)."""
        counts = {0: 0}
        for current in self._reachable([node]):
            rule = self.rules[current]
            counts[current] = (int(abs(rule[1]) == generator) if rule[0] == 't'
                               else counts[rule[1]]+counts[rule[2]])
        count, position = counts[node], 0
        if not count:
            return 0, None, None
        current = node
        while self.rules[current][0] == 'c':
            self.tick()
            _, a, b = self.rules[current]
            if counts[a]:
                current = a
            else:
                position += self.lengths[a]
                current = b
        return count, position, self.rules[current][1]

    def singletons(self, roots):
        """Generators occurring exactly once in each root, using shared masks.

        Presence P and repetition R combine as P=P1|P2 and
        R=R1|R2|(P1&P2). Dense bit positions avoid dependence on letter labels.
        """
        reachable = self._reachable(roots)
        labels = sorted({abs(self.rules[node][1]) for node in reachable
                         if self.rules[node][0] == 't'})
        bits = {g: 1 << i for i, g in enumerate(labels)}
        present, repeated = {0: 0}, {0: 0}
        for node in reachable:
            self.tick()
            rule = self.rules[node]
            if rule[0] == 't':
                present[node], repeated[node] = bits[abs(rule[1])], 0
            else:
                _, a, b = rule
                present[node] = present[a] | present[b]
                repeated[node] = repeated[a] | repeated[b] | (present[a] & present[b])
        result = []
        for root in roots:
            self.tick()
            mask, values = present[root] & ~repeated[root], []
            while mask:
                self.tick()
                bit = mask & -mask
                values.append(labels[bit.bit_length()-1])
                mask ^= bit
            result.append(values)
        return result

    def summarize(self, roots, *, whitehead=False):
        """Absolute-letter counts and optional cyclic Whitehead graph.

        Propagate occurrence multiplicities down the shared DAG. Every concat
        contributes its boundary pair with that multiplicity; each nonempty
        root contributes one closing pair. No expanded letters are visited.
        Costs O(N log N + m) abstract operations including topological sorting,
        for N reachable rules and m roots, with exact integer arithmetic.
        """
        weights, counts, graph = defaultdict(int), defaultdict(int), {}

        def edge(x, y, weight):
            # The automorphism convention uses {x, -y}, not {-x, y}.
            y = -y
            graph.setdefault(x, {})
            graph.setdefault(y, {})
            graph[x][y] = graph[x].get(y, 0)+weight
            graph[y][x] = graph[y].get(x, 0)+weight

        for root in roots:
            self.tick()
            if root:
                weights[root] += 1
                if whitehead:
                    edge(self.last[root], self.first[root], 1)
        for node in reversed(self._reachable(roots)):
            self.tick()
            rule, weight = self.rules[node], weights[node]
            if rule[0] == 't':
                counts[abs(rule[1])] += weight
                if whitehead:
                    graph.setdefault(rule[1], {})
                    graph.setdefault(-rule[1], {})
            else:
                _, a, b = rule
                weights[a] += weight
                weights[b] += weight
                if whitehead:
                    edge(self.last[a], self.first[b], weight)
        return dict(counts), graph

    def expand(self, node, *, limit=100000):
        """Bounded debugging oracle; never called by compressed operations."""
        if self.lengths[node] > limit:
            raise CompressedLimit('explicit debug expansion allowance exhausted')
        pending, result = [node], []
        while pending:
            self.tick()
            current = pending.pop()
            if not current:
                continue
            rule = self.rules[current]
            if rule[0] == 't':
                result.append(rule[1])
            else:
                pending.extend((rule[2], rule[1]))
        return result
