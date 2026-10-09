"""Reference implementation of raw singleton elimination in signed circuits.

This is a research representation prototype, not a knot-recognition API.
Concatenations are immutable. Positive and negative handles share one node;
a negative handle means formal word inversion. A generator receives at most
one binding. Subsequent bindings automatically update every retained root.
No free reduction, equality oracle, or expanded-word scan is used by eliminate.
"""
from collections import deque


class CircuitLimit(RuntimeError):
    pass


class SignedCircuit:
    def __init__(self, *, max_nodes=1_000_000, max_work=100_000_000):
        self.rules = [None]
        self.depths = [0]  # concatenation height with bindings ignored
        self.generators = {}
        self.bindings = {}  # generator -> signed handle
        self.interned = {}
        self.max_nodes = max_nodes
        self.max_work = max_work
        self.work = 0
        self.eliminations = 0
        self.context_siblings = 0

    def tick(self, amount=1):
        self.work += amount
        if self.work > self.max_work:
            raise CircuitLimit('persistent-circuit work allowance exhausted')

    def _intern(self, rule, depth):
        self.tick()
        if rule in self.interned:
            return self.interned[rule]
        if len(self.rules)-1 >= self.max_nodes:
            raise CircuitLimit('persistent-circuit node allowance exhausted')
        node = len(self.rules)
        self.rules.append(rule)
        self.depths.append(depth)
        self.interned[rule] = node
        return node

    def letter(self, value):
        if type(value) is not int or value == 0:
            raise ValueError('letters must be nonzero signed integers')
        g = abs(value)
        if g not in self.generators:
            self.generators[g] = self._intern(('t', g), 0)
        node = self.generators[g]
        return node if value > 0 else -node

    def concat(self, left, right):
        if not left:
            return right
        if not right:
            return left
        return self._intern(('c', left, right),
                            1+max(self.depths[abs(left)], self.depths[abs(right)]))

    def balanced(self, handles):
        nodes = [node for node in handles if node]
        while len(nodes) > 1:
            nodes = [self.concat(nodes[i], nodes[i+1])
                     if i+1 < len(nodes) else nodes[i]
                     for i in range(0, len(nodes), 2)]
        return nodes[0] if nodes else 0

    def from_word(self, word):
        return self.balanced(self.letter(x) for x in word)

    def _children(self, node):
        rule = self.rules[node]
        if rule[0] == 'c':
            return [abs(rule[1]), abs(rule[2])]
        target = self.bindings.get(rule[1])
        return [] if target is None or target == 0 else [abs(target)]

    def topological(self):
        """Dependencies first, including forward generator bindings.

        Kahn's method is used deliberately: allocation order ceases to be a
        topological order after the first binding. Duplicate child edges are
        retained in both incidence lists, so repeated subwords remain exact.
        """
        n = len(self.rules)
        degree = [0]*n
        users = [[] for _ in range(n)]
        for node in range(1, n):
            self.tick()
            children = self._children(node)
            degree[node] = len(children)
            for child in children:
                users[child].append(node)
        queue = deque(node for node in range(1, n) if degree[node] == 0)
        order = []
        while queue:
            self.tick()
            node = queue.popleft()
            order.append(node)
            for user in users[node]:
                degree[user] -= 1
                if degree[user] == 0:
                    queue.append(user)
        if len(order) != n-1:
            raise ArithmeticError('cyclic generator binding graph')
        return order

    def capped_occurrences(self, generator):
        """Exact counts in {0, 1, at-least-2}; orientation is immaterial."""
        counts = [0]*len(self.rules)
        for node in self.topological():
            self.tick()
            rule = self.rules[node]
            if rule[0] == 'c':
                counts[node] = min(2, counts[abs(rule[1])]+counts[abs(rule[2])])
            elif rule[1] in self.bindings:
                counts[node] = counts[abs(self.bindings[rule[1]])]
            else:
                counts[node] = int(rule[1] == generator)
        return counts

    def eliminate(self, roots, slot, generator):
        """Solve one singleton equation and drop its original relator slot.

        Returns the signed image handle. roots is updated only after the
        complete image has been constructed; a failed precondition never
        installs a binding. Images remain raw, including cancelling letters.
        """
        if (type(slot) is not int or not 0 <= slot < len(roots)
                or type(generator) is not int or generator <= 0
                or generator not in self.generators
                or generator in self.bindings):
            raise ValueError('invalid singleton-elimination request')
        counts = self.capped_occurrences(generator)
        current = roots[slot]
        if counts[abs(current)] != 1:
            raise ValueError('donor does not contain this live generator exactly once')
        prefix, suffix = [], []
        while True:
            self.tick()
            orientation = 1 if current > 0 else -1
            rule = self.rules[abs(current)]
            if rule[0] == 't':
                g = rule[1]
                if g in self.bindings:
                    current = orientation*self.bindings[g]
                    continue
                if g != generator:
                    raise ArithmeticError('singleton descent reached another letter')
                signed_occurrence = orientation
                break
            _, left, right = rule
            if orientation < 0:
                left, right = -right, -left
            if counts[abs(left)]:
                # Exactly one occurrence in the parent forces right to be x-free.
                suffix.append(right)
                current = left
            else:
                prefix.append(left)
                current = right
        siblings = list(reversed(suffix))+prefix  # R followed by L
        self.context_siblings += len(siblings)
        rest = self.balanced(siblings)
        image = -rest if signed_occurrence > 0 else rest
        # Every sibling is x-free in the old binding DAG. Therefore this edge
        # cannot introduce a directed cycle.
        self.bindings[generator] = image
        roots[slot] = 0
        self.eliminations += 1
        return image

    def measurements(self, roots):
        lengths = [0]*len(self.rules)
        height = [0]*len(self.rules)
        for node in self.topological():
            self.tick()
            rule = self.rules[node]
            if rule[0] == 'c':
                a, b = abs(rule[1]), abs(rule[2])
                lengths[node] = lengths[a]+lengths[b]
                height[node] = 1+max(height[a], height[b])
            elif rule[1] in self.bindings:
                target = abs(self.bindings[rule[1]])
                lengths[node] = lengths[target]
                height[node] = 1+height[target]
            else:
                lengths[node] = 1
        return dict(nodes=len(self.rules)-1,
                    binding_free_height=max(self.depths),
                    full_height=max(height),
                    max_length_bits=max(x.bit_length() for x in lengths),
                    root_lengths=[lengths[abs(root)] for root in roots],
                    context_siblings=self.context_siblings,
                    eliminations=self.eliminations, work=self.work)

    def export_slp(self, roots):
        """Materialize an ordinary binary SLP once, in dependency order.

        Its terminals contain signed *letters*, while all node references are
        nonnegative. Bound-generator vertices become aliases. Each old concat
        creates at most two output concats, one for each orientation. The
        exported object has no mutable bindings or signed node references.
        """
        output, mapped = [None], {0: 0}

        def append_concat(a, b):
            if not a:
                return b
            if not b:
                return a
            output.append(('c', a, b))
            return len(output)-1

        for node in self.topological():
            self.tick()
            rule = self.rules[node]
            if rule[0] == 'c':
                a, b = rule[1:]
                mapped[node] = append_concat(mapped[a], mapped[b])
                mapped[-node] = append_concat(mapped[-b], mapped[-a])
            elif rule[1] in self.bindings:
                target = self.bindings[rule[1]]
                mapped[node], mapped[-node] = mapped[target], mapped[-target]
            else:
                output.append(('t', rule[1]))
                mapped[node] = len(output)-1
                output.append(('t', -rule[1]))
                mapped[-node] = len(output)-1
        return dict(rules=output, roots=[mapped[root] for root in roots])

    def expand(self, root, *, limit=100_000):
        """Bounded testing oracle; eliminate never calls this method."""
        length = self.measurements([root])['root_lengths'][0]
        if length > limit:
            raise CircuitLimit('literal expansion allowance exhausted')
        pending, result = [root], []
        while pending:
            self.tick()
            node = pending.pop()
            if not node:
                continue
            sign = 1 if node > 0 else -1
            rule = self.rules[abs(node)]
            if rule[0] == 't':
                if rule[1] in self.bindings:
                    pending.append(sign*self.bindings[rule[1]])
                else:
                    result.append(sign*rule[1])
            elif sign > 0:
                pending.extend((rule[2], rule[1]))
            else:
                pending.extend((-rule[1], -rule[2]))
        return result


def doubling_context_family(k):
    """An explicit presentation with exponentially growing raw donor contexts.

    Let a=1,b=2,x_i=i+3,z=k+4. Initially r_0=x_0^-1 a x_1 b,
    r_i=x_0^-1 x_(i+1) for 1<=i<k, and a retained r_k=x_0^-1 z.
    Eliminate x_i using r_i, i=0,...,k-1. The retained raw length is
    2^k+2, despite a source of O(k) letters. This is an artificial
    presentation benchmark, not a family of hard knot diagrams.
    """
    if type(k) is not int or k < 1:
        raise ValueError('k must be positive')
    words = [[-3, 1, 4, 2]]
    words += [[-3, i+4] for i in range(1, k)]
    words += [[-3, k+4]]
    return words, [(i, i+3) for i in range(k)]
