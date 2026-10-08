"""Exact straight-line-program words and compressed free-group reduction.

Equality uses split/periodicity-compaction assertions (Plandowski, as exposed
in Schleimer, arXiv:math/0608563, Section 8). No hashes or expanded-string
comparisons decide equality. Slicing and boundary cancellation implement the
compressed free-group reduction of the same paper. Resource caps interrupt;
they never substitute a probabilistic or incomplete equality answer.
"""
from collections import defaultdict
from math import gcd


class CompressedLimit(RuntimeError):
    pass


class WordArena:
    """Interned binary SLPs; node zero is empty, signed integers are letters.

    ``max_nodes`` also bounds live equality assertions and the equality cache.
    ``max_work`` charges cooperative abstract operations, not CPU instructions.
    All public word arguments are node ids obtained from this arena.
    """
    def __init__(self, *, max_nodes=100000, max_work=10000000, check=lambda: None):
        for name, value in (('max_nodes', max_nodes), ('max_work', max_work)):
            if type(value) is not int or value < 0:
                raise ValueError(f'{name} must be a nonnegative integer')
        self.max_nodes, self.left, self.check = max_nodes, max_work, check
        self.rules, self.lengths, self.first, self.last = [None], [0], [0], [0]
        self._interned, self._inverse, self._reduced, self._equal_cache = {}, {0: 0}, {0: 0}, {}
        self.stats = dict(work=0, equality_calls=0, splits=0, compact_triples=0, peak_assertions=0)

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
        gamma = {((0, a), (1, b), 0)}

        class Mismatch(Exception):
            pass

        def add(out, u, v, offset):
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
            out.add((u, v, offset))
            if len(out) > self.max_nodes:
                raise CompressedLimit('compressed equality assertion allowance exhausted')

        try:
            while gamma:
                self.tick(len(gamma))
                self.stats['peak_assertions'] = max(self.stats['peak_assertions'], len(gamma))
                nodes = {x for u, v, _ in gamma for x in (u, v) if self.rules[x[1]][0] == 'c'}
                selected = max(nodes, key=lambda x: (self.lengths[x[1]], x))
                side, index = selected
                _, aa, bb = self.rules[index]
                left, right, middle = (side, aa), (side, bb), self.lengths[aa]
                out = set()
                for u, v, offset in gamma:
                    if u == selected:
                        end = min(self.lengths[u[1]], offset+self.lengths[v[1]])
                        if offset < middle:
                            add(out, left, v, offset)
                        if end > middle:
                            if offset >= middle:
                                add(out, right, v, offset-middle)
                            else:
                                add(out, v, right, middle-offset)
                    elif v == selected:
                        add(out, u, left, offset)
                        if self.lengths[u[1]] > offset+middle:
                            add(out, u, right, offset+middle)
                    else:
                        add(out, u, v, offset)
                groups, gamma = defaultdict(set), set()
                for u, v, offset in out:
                    self.tick()
                    if self.lengths[u[1]] <= offset+self.lengths[v[1]]:
                        groups[u, v].add(offset)
                    else:
                        gamma.add((u, v, offset))
                for (u, v), offsets in groups.items():
                    while True:
                        self.tick(len(offsets)+1)
                        values = sorted(offsets)
                        for k in range(len(values)-2):
                            self.tick()
                            i, j, last = values[k:k+3]
                            if j+last-i <= self.lengths[u[1]]:
                                offsets.remove(j)
                                offsets.remove(last)
                                offsets.add(i+gcd(j-i, last-i))
                                self.stats['compact_triples'] += 1
                                break
                        else:
                            break
                    gamma.update((u, v, i) for i in offsets)
                self.stats['splits'] += 1
            result = True
        except Mismatch:
            result = False
        if len(self._equal_cache) >= self.max_nodes:
            self._equal_cache.clear()
        self._equal_cache[key] = result
        self.tick()
        return result

    def lcp(self, a, b, cap=None):
        """Exact longest common prefix; logarithmically many equality queries."""
        hi = min(self.lengths[a], self.lengths[b])
        if cap is not None:
            if type(cap) is not int or cap < 0:
                raise ValueError('prefix cap must be a nonnegative integer')
            hi = min(hi, cap)
        if not hi or self.first[a] != self.first[b]:
            self.tick()
            return 0
        lo = 0
        while lo < hi:
            self.tick()
            mid = (lo+hi+1)//2
            if self.equal(self.slice(a, 0, mid), self.slice(b, 0, mid)):
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
