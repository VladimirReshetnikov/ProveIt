"""Straight-line programs of commuting, idempotent full-port cones.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from dataclasses import dataclass
from .profiles import exact_int
from .quotients import QuotientEngine, atom_group


def join_blocks(m, *collections):
    parent = list(range(m))
    rank = [0] * m
    active = set()
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for blocks in collections:
        for block in blocks:
            if not block:
                continue
            active.update(block)
            root = find(block[0])
            for a in block[1:]:
                root, other = find(root), find(a)
                if root == other:
                    continue
                if rank[root] < rank[other]:
                    root, other = other, root
                parent[other] = root
                if rank[root] == rank[other]:
                    rank[root] += 1
    grouped = {}
    for a in sorted(active):
        grouped.setdefault(find(a), []).append(a)
    return tuple(sorted(tuple(v) for v in grouped.values()))


@dataclass(frozen=True)
class ProgramNode:
    op: str
    atoms: tuple[int, ...] = ()
    left: int = -1
    right: int = -1
    exponent: int = 0


class ConeProgram:
    def __init__(self, m, records, root=None):
        if type(m) is not int or m < 0 or not isinstance(records, (list, tuple)):
            raise ValueError('nonnegative atom count and an explicit program required')
        self.m = m
        self.nodes = []
        self.lengths = []
        self.summaries = []
        def reference(value, limit):
            value = exact_int(value)
            if not 0 <= value < limit:
                raise ValueError('program references must point strictly backwards')
            return value
        for i, record in enumerate(records):
            if not isinstance(record, dict):
                raise ValueError('malformed program node')
            op = record.get('op')
            if op == 'cone' and set(record) == {'op', 'atoms'}:
                group = atom_group(record['atoms'], m)
                node = ProgramNode(op, atoms=group)
                length, summary = 1, (group,) if group else ()
            elif op == 'concat' and set(record) == {'op', 'left', 'right'}:
                a, b = reference(record['left'], i), reference(record['right'], i)
                node = ProgramNode(op, left=a, right=b)
                length = self.lengths[a] + self.lengths[b]
                summary = join_blocks(m, self.summaries[a], self.summaries[b])
            elif op == 'power' and set(record) == {'op', 'child', 'exponent'}:
                a, p = reference(record['child'], i), exact_int(record['exponent'])
                if p < 0:
                    raise ValueError('exponents must be nonnegative')
                node = ProgramNode(op, left=a, exponent=p)
                length = self.lengths[a] * p
                summary = self.summaries[a] if p else ()
            else:
                raise ValueError('unknown program node or extraneous fields')
            self.nodes.append(node)
            self.lengths.append(length)
            self.summaries.append(summary)
        if not self.nodes:
            raise ValueError('use a zero power for an empty program')
        self.root = len(self.nodes) - 1 if root is None else exact_int(root)
        if not 0 <= self.root < len(self.nodes):
            raise ValueError('invalid root')
        self.nodes = tuple(self.nodes)
        self.lengths = tuple(self.lengths)
        self.summaries = tuple(self.summaries)

    @property
    def length(self):
        return self.lengths[self.root]

    def to_records(self):
        out = []
        for n in self.nodes:
            if n.op == 'cone':
                out.append(dict(op=n.op, atoms=list(n.atoms)))
            elif n.op == 'concat':
                out.append(dict(op=n.op, left=n.left, right=n.right))
            else:
                out.append(dict(op=n.op, child=n.left, exponent=n.exponent))
        return out

    def prefix_summary(self, length):
        length = exact_int(length)
        if not 0 <= length <= self.length:
            raise ValueError('prefix length is outside the expanded program')
        node, result = self.root, ()
        while length:
            if length == self.lengths[node]:
                return join_blocks(self.m, result, self.summaries[node])
            n = self.nodes[node]
            if n.op == 'concat':
                left_length = self.lengths[n.left]
                if length <= left_length:
                    node = n.left
                else:
                    result = join_blocks(self.m, result, self.summaries[n.left])
                    length -= left_length
                    node = n.right
            elif n.op == 'power':
                child_length = self.lengths[n.left]
                if child_length and length >= child_length:
                    return join_blocks(self.m, result, self.summaries[n.left])
                node = n.left
            else:
                raise ArithmeticError('nonintegral cone prefix')
        return result

    def evaluate(self, profiles, prefix=None):
        if len(profiles.lengths) != self.m:
            raise ValueError('program and profile atoms differ')
        state = QuotientEngine(profiles)
        blocks = self.summaries[self.root] if prefix is None else self.prefix_summary(prefix)
        state.apply_blocks(blocks)
        return state

    def first_at_most(self, profiles, target):
        """Locate the first prefix with count <= target by a grammar descent.

        The number of state trials is at most the DAG node count plus one,
        even when the expanded program length has thousands of bits.
        """
        target = exact_int(target)
        if len(profiles.lengths) != self.m:
            raise ValueError('program and profile atoms differ')
        current = QuotientEngine(profiles)
        trials = 0
        if current.count <= target:
            return dict(index=0, count=current.count, trials=trials)
        trial = current.clone()
        trial.apply_blocks(self.summaries[self.root])
        trials += 1
        if trial.count > target:
            return dict(index=None, count=trial.count, trials=trials)
        node, offset = self.root, 0
        while True:
            n = self.nodes[node]
            if n.op == 'cone':
                current.cone(n.atoms)
                if current.count > target:
                    raise ArithmeticError('threshold descent invariant failed')
                return dict(index=offset + 1, count=current.count, trials=trials)
            if n.op == 'power':
                if n.exponent == 0:
                    raise ArithmeticError('a zero power cannot be the first crossing')
                node = n.left  # idempotence puts the first crossing in copy one
            else:
                trial = current.clone()
                trial.apply_blocks(self.summaries[n.left])
                trials += 1
                if trial.count <= target:
                    node = n.left
                else:
                    current = trial
                    offset += self.lengths[n.left]
                    node = n.right

    def change_points(self, profiles):
        """All count-changing expanded steps without expanding repetitions.

        At most 2*m-1 events are possible for m>0. Unchanged subprograms
        are skipped. A positive power needs only its first copy because the
        fixed-source cone action is idempotent. Counts refer to old points.
        """
        if len(profiles.lengths) != self.m:
            raise ValueError('program and profile atoms differ')
        current = QuotientEngine(profiles)
        stack = [(self.root, 0)]
        events, trials = [], 0
        while stack:
            node, offset = stack.pop()
            trial = current.clone()
            trial.apply_blocks(self.summaries[node])
            trials += 1
            if trial.count == current.count:
                continue
            n = self.nodes[node]
            if n.op == 'cone':
                before = current.count
                current = trial
                events.append(dict(index=offset + 1, before=before, after=current.count))
            elif n.op == 'concat':
                stack.append((n.right, offset + self.lengths[n.left]))
                stack.append((n.left, offset))
            else:
                if n.exponent <= 0:
                    raise ArithmeticError('empty repetition changed a partition')
                stack.append((n.left, offset))
        if len(events) > max(0, 2*self.m - 1):
            raise ArithmeticError('fixed-atom semilattice height bound failed')
        return dict(events=events, count=current.count, trials=trials)
