"""Deterministic SLP strings: a source-derived subset of ProveIt's WordArena.

The indexed split/periodicity-compaction equality procedure is adapted from
fast/fastunknot/compressed_words.py at commit 47002f64b9a97f64edc8e8b8f793b83983b719f9
(blob bd68418e226813a7fa50dc87405c214970ddf50e).  This is not a byte-identical
snapshot, nor the whole maintained module. No probabilistic fingerprints.
Upstream and this adaptation are MIT-0. See provenance/SOURCES.md.
"""
from collections import defaultdict
from heapq import heappop, heappush
from math import gcd


class Limit(RuntimeError):
    """A resource cap was reached; no mathematical verdict is implied."""


class Arena:
    def __init__(self, *, max_nodes=1000000, max_work=50000000,
                 equality_probe_steps=64, prefix_probe_steps=64,
                 check=lambda: None):
        for value in (max_nodes, max_work, equality_probe_steps, prefix_probe_steps):
            if type(value) is not int or value < 0:
                raise ValueError('caps must be nonnegative integers')
        self.max_nodes, self.left, self.check = max_nodes, max_work, check
        self.equality_probe_steps = equality_probe_steps
        self.prefix_probe_steps = prefix_probe_steps
        self.rules, self.lengths, self.first, self.last = [None], [0], [0], [0]
        self.uniform, self.heights = [0], [0]
        self._interned, self._equal_cache = {}, {}
        self.stats = dict(work=0, equality_calls=0, splits=0, compact_triples=0,
                          peak_assertions=0, probe_steps=0, probe_resolved=0,
                          probe_fallbacks=0, lcp_calls=0, lcp_probe_steps=0,
                          lcp_probe_resolved=0, lcp_probe_fallbacks=0)

    def tick(self, amount=1):
        self.check()
        self.left -= amount
        self.stats['work'] += amount
        if self.left < 0:
            raise Limit('SLP work allowance exhausted')

    def _intern(self, rule, length, first, last):
        self.tick()
        known = self._interned.get(rule)
        if known is not None:
            return known
        if len(self.rules) - 1 >= self.max_nodes:
            raise Limit('SLP node allowance exhausted')
        result = len(self.rules)
        self.rules.append(rule)
        self.lengths.append(length)
        self.first.append(first)
        self.last.append(last)
        if rule[0] == 't':
            self.uniform.append(first)
            self.heights.append(1)
        else:
            a, b = rule[1:]
            self.uniform.append(self.uniform[a] if self.uniform[a] == self.uniform[b] else 0)
            self.heights.append(1 + max(self.heights[a], self.heights[b]))
        self._interned[rule] = result
        return result

    def letter(self, value):
        if type(value) is not int or value == 0:
            raise ValueError('nonzero integer letter required')
        return self._intern(('t', value), 1, value, value)

    def concat(self, left, right):
        self.tick()
        if not left:
            return right
        if not right:
            return left
        return self._intern(('c', left, right), self.lengths[left] + self.lengths[right],
                            self.first[left], self.last[right])

    def from_word(self, letters):
        nodes = [self.letter(x) for x in letters]
        while len(nodes) > 1:
            nodes = [self.concat(nodes[i], nodes[i + 1]) if i + 1 < len(nodes) else nodes[i]
                     for i in range(0, len(nodes), 2)]
        return nodes[0] if nodes else 0

    def slice(self, node, start, stop):
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
                    parts.append((b, max(0, lo - middle), hi - middle))
                if ready:
                    done[key] = (done[parts[0]] if len(parts) == 1
                                 else self.concat(done[parts[0]], done[parts[1]]))
                else:
                    pending.append((current, lo, hi, True))
                    pending.extend((*part, False) for part in parts if part not in done)
        return done[node, start, stop]

    def _prefix_probe(self, a, b, cap, steps, counter):
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

    def _remember_equal(self, key, result):
        if len(self._equal_cache) >= self.max_nodes:
            self._equal_cache.clear()
        self._equal_cache[key] = result
        self.tick()
        return result

    def equal(self, a, b):
        """Exact polynomial SLP equality via indexed assertions and compaction."""
        self.tick()
        self.stats['equality_calls'] += 1
        if a == b:
            return True
        if (self.lengths[a] != self.lengths[b] or self.first[a] != self.first[b]
                or self.last[a] != self.last[b]):
            return False
        if self.uniform[a] and self.uniform[a] == self.uniform[b]:
            return True
        key = min(a, b), max(a, b)
        if key in self._equal_cache:
            return self._equal_cache[key]
        if self.equality_probe_steps:
            matched, resolved = self._prefix_probe(a, b, self.lengths[a],
                                                   self.equality_probe_steps, 'probe_steps')
            if resolved:
                self.stats['probe_resolved'] += 1
                return self._remember_equal(key, matched == self.lengths[a])
            self.stats['probe_fallbacks'] += 1
        gamma, mentioned, overlaps = set(), defaultdict(set), defaultdict(set)
        pending, queued, dirty = [], set(), set()

        class Mismatch(Exception):
            pass

        def add(u, v, offset):
            self.tick()
            if offset == 0 and u[1] == v[1]:
                return
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
                raise Limit('equality assertion allowance exhausted')
            self.stats['peak_assertions'] = max(self.stats['peak_assertions'], len(gamma))
            for node in (u, v):
                mentioned[node].add(assertion)
                if self.rules[node[1]][0] == 'c' and node not in queued:
                    heappush(pending, (-self.lengths[node[1]], -node[0], -node[1]))
                    queued.add(node)
            if self.lengths[u[1]] <= offset + self.lengths[v[1]]:
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
            if self.lengths[u[1]] <= offset + self.lengths[v[1]]:
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
                    continue
                side, index = selected
                _, aa, bb = self.rules[index]
                left, right, middle = (side, aa), (side, bb), self.lengths[aa]
                affected = list(mentioned[selected])
                for assertion in affected:
                    remove(assertion)
                for u, v, offset in affected:
                    if u == selected:
                        end = min(self.lengths[u[1]], offset + self.lengths[v[1]])
                        if offset < middle:
                            add(left, v, offset)
                        if end > middle:
                            if offset >= middle:
                                add(right, v, offset - middle)
                            else:
                                add(v, right, middle - offset)
                    elif v == selected:
                        add(u, left, offset)
                        if self.lengths[u[1]] > offset + middle:
                            add(u, right, offset + middle)
                while dirty:
                    u, v = dirty.pop()
                    while True:
                        values = sorted(overlaps.get((u, v), ()))
                        self.tick(len(values) + 1)
                        for k in range(len(values) - 2):
                            self.tick()
                            i, j, last = values[k:k + 3]
                            if j + last - i <= self.lengths[u[1]]:
                                remove((u, v, j))
                                remove((u, v, last))
                                add(u, v, i + gcd(j - i, last - i))
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
        self.stats['lcp_calls'] += 1
        hi = min(self.lengths[a], self.lengths[b])
        if cap is not None:
            if type(cap) is not int or cap < 0:
                raise ValueError('invalid prefix cap')
            hi = min(hi, cap)
        if a == b:
            self.tick()
            return hi
        if not hi or self.first[a] != self.first[b]:
            self.tick()
            return 0
        if self.uniform[a] and self.uniform[a] == self.uniform[b]:
            return hi
        lo = 0
        if self.prefix_probe_steps:
            lo, resolved = self._prefix_probe(a, b, hi, self.prefix_probe_steps,
                                               'lcp_probe_steps')
            if resolved:
                self.stats['lcp_probe_resolved'] += 1
                return lo
            self.stats['lcp_probe_fallbacks'] += 1
        while lo < hi:
            self.tick()
            mid = (lo + hi + 1) // 2
            if self.equal(self.slice(a, lo, mid), self.slice(b, lo, mid)):
                lo = mid
            else:
                hi = mid - 1
        return lo

    def expand(self, node, *, limit=100000):
        if self.lengths[node] > limit:
            raise Limit('debug expansion cap exceeded')
        pending, result = [node], []
        while pending:
            current = pending.pop()
            if not current:
                continue
            rule = self.rules[current]
            if rule[0] == 't':
                result.append(rule[1])
            else:
                pending.extend((rule[2], rule[1]))
        return result
