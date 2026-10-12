"""Exact weighted minimum deferral by ordered incidence interfaces.

Invariant: a state stores the active bag vertices in the restriction of a
possible topological order, and the vertices whose pivot edge is processed.
No transitive-closure matrix is stored. Costs are paid only at forgetting.
"""
from collections import defaultdict
from dataclasses import dataclass
from .model import Matrix, Check, noop
from .decomposition import Decomposition, validate, elimination_decomposition
from .certificates import package_plan

class ResourceLimit(RuntimeError):
    pass

@dataclass
class Limits:
    max_states: int | None = 250_000
    max_work: int | None = 20_000_000
    max_width: int | None = 9

    def validate(self):
        for name in ('max_states', 'max_work', 'max_width'):
            x = getattr(self, name)
            if x is not None and (type(x) is not int or x < 0):
                raise ValueError('limits must be nonnegative integers or None')


class Engine:
    def __init__(self, matrix: Matrix, limits: Limits, check: Check):
        self.matrix, self.limits, self.check = matrix, limits, check
        self.labels, self.adj, self.edges = matrix.graph()
        self.stats = dict(work=0, peak_states=0, transitions=0, joins=0,
                          edge_events=0, order_groups=0)
        self.recipes = [('empty',)]

    def tick(self):
        self.stats['work'] += 1
        if self.stats['work'] % 256 == 1:
            self.check()
        if self.limits.max_work is not None and self.stats['work'] > self.limits.max_work:
            raise ResourceLimit('candidate-work limit')

    def put(self, table, key, value):
        old = table.get(key)
        if old is None or value[0] < old[0]:
            table[key] = value
            if self.limits.max_states is not None and len(table) > self.limits.max_states:
                raise ResourceLimit('state-table limit')

    def done(self, table):
        self.stats['peak_states'] = max(self.stats['peak_states'], len(table))
        self.stats['transitions'] += 1
        self.check()
        return table

    def introduce(self, table, v):
        out = {}
        for (order, matched), val in table.items():
            self.tick(); self.put(out, (order, matched), val)  # inactive
            for pos in range(len(order)+1):
                self.tick()
                self.put(out, (order[:pos] + (v,) + order[pos:], matched), val)
        return self.done(out)

    def forget(self, table, v):
        out = {}; bit = 1 << v
        kind, label = self.labels[v]
        for (order, matched), (cost, recipe) in table.items():
            self.tick()
            if v in order:
                if matched & bit:
                    key = (tuple(x for x in order if x != v), matched & ~bit)
                    self.put(out, key, (cost, recipe))
            elif kind == 'r':
                key = (order, matched)
                newcost = (cost[0] + self.matrix.weights[label], cost[1] + 1)
                old = out.get(key)
                if old is None or newcost < old[0]:
                    newrecipe = len(self.recipes)
                    self.recipes.append(('defer', label, recipe))
                    self.put(out, key, (newcost, newrecipe))
            else:
                self.put(out, (order, matched), (cost, recipe))
        return self.done(out)

    def edge(self, table, u, v, eligible):
        out = {}; bits = (1 << u) | (1 << v)
        self.stats['edge_events'] += 1
        for (order, matched), val in table.items():
            self.tick()
            if u not in order or v not in order or order.index(u) < order.index(v):
                self.put(out, (order, matched), val)
            elif eligible and not matched & bits:
                self.put(out, (order, matched | bits), val)
        return self.done(out)

    def join(self, left, right):
        # Matching equality of total orders is essential, not merely equality
        # of active sets. A shared ordering amalgamates all private vertices.
        groups = defaultdict(list)
        for (order, mask), val in right.items():
            groups[order].append((mask, val))
        out = {}; self.stats['joins'] += 1
        self.stats['order_groups'] += len(groups)
        for (order, a), (ca, ra) in left.items():
            for b, (cb, rb) in groups.get(order, ()):
                self.tick()
                if a & b:
                    continue
                key = (order, a | b); cost = (ca[0]+cb[0], ca[1]+cb[1])
                old = out.get(key)
                if old is None or cost < old[0]:
                    if ra == 0:
                        recipe = rb
                    elif rb == 0:
                        recipe = ra
                    else:
                        recipe = len(self.recipes)
                        self.recipes.append(('join', ra, rb))
                    self.put(out, key, (cost, recipe))
        return self.done(out)

    def transform(self, table, oldbag, newbag):
        for v in sorted(set(oldbag) - set(newbag)):
            table = self.forget(table, v)
        for v in sorted(set(newbag) - set(oldbag)):
            table = self.introduce(table, v)
        return table

    def solve(self, td):
        root, children, preorder = validate(td, self.adj)
        self.stats['width'] = td.width
        if self.limits.max_width is not None and td.width > self.limits.max_width:
            raise ResourceLimit('supplied-width limit')
        depth = {root: 0}
        for i in preorder:
            for j in children[i]:
                depth[j] = depth[i] + 1
        occurs = [set() for _ in self.labels]
        for i, bag in enumerate(td.bags):
            for v in bag:
                occurs[v].add(i)
        owned = [[] for _ in td.bags]
        for edge in self.edges:
            u, v, _ = edge
            owner = min(occurs[u] & occurs[v], key=lambda i: depth[i])
            owned[owner].append(edge)
        tables = {}
        for i in reversed(preorder):
            bag = td.bags[i]
            if children[i]:
                parts = []
                for child in children[i]:
                    parts.append(self.transform(tables.pop(child), td.bags[child], bag))
                table = parts[0]
                for other in parts[1:]:
                    table = self.join(table, other)
            else:
                table = {((), 0): ((0, 0), 0)}
                table = self.transform(table, (), bag)
            for edge in owned[i]:
                table = self.edge(table, *edge)
            tables[i] = table
        table = self.transform(tables[root], td.bags[root], ())
        (cost, recipe) = table[((), 0)]
        deferred = set(); stack = [recipe]
        while stack:
            item = self.recipes[stack.pop()]
            if item[0] == 'defer':
                if item[1] in deferred:
                    raise ArithmeticError('duplicate forgotten row in witness')
                deferred.add(item[1]); stack.append(item[2])
            elif item[0] == 'join':
                stack.extend(item[1:])
        self.stats['recipe_nodes'] = len(self.recipes)
        self.stats['bags'] = len(td.bags)
        plan = package_plan(self.matrix, deferred, method='ordered-interface-dp',
                            stats=self.stats, check=self.check)
        if (plan['cost'], len(plan['deferred_rows'])) != cost:
            raise ArithmeticError('cost/backpointer mismatch')
        plan['decomposition'] = td.to_dict()
        plan['decomposition_scope_rows'] = list(self.matrix.rows)
        return plan


def ordered_plan(counts: dict, weights: dict | None = None,
                 decomposition: Decomposition | None = None, *,
                 limits: Limits | None = None, check: Check = noop) -> dict:
    matrix = Matrix.parse(counts, weights)
    limits = limits or Limits(); limits.validate(); check()
    engine = Engine(matrix, limits, check)
    if decomposition is None:
        decomposition = elimination_decomposition(engine.adj, check=check)
    try:
        return engine.solve(decomposition)
    except ResourceLimit as exc:
        return dict(status='RESOURCE_LIMIT', reason=str(exc), stats=engine.stats,
                    trust='no infeasibility or topological conclusion')
