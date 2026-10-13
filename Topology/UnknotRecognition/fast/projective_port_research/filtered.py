"""Complete predicate-filtered extreme-ray discovery on a common-port atlas.

An excluded support S means that some coordinate in S must vanish. At each
atlas vertex a union-mask dynamic program enforces these clauses across all
blocks. The extra factor is at most 2**q for q rejected supports, not a product
of local mode counts. This research adapter does not bound q geometrically.
"""
from fractions import Fraction as Q

from .common import IntrinsicPrepared, extreme_witness, verify_vector
from projective_ports.exact import rational, dot


class FilterLimit(RuntimeError):
    """Incomplete predicate search; never a negative query."""


class Budget:
    def __init__(self, limit, check):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError('max_transitions must be a nonnegative integer or None')
        self.limit, self.callback = limit, check
        self.transitions = 0
        self.callback_failed = False

    def check(self):
        try:
            self.callback()
        except BaseException:
            self.callback_failed = True
            raise

    def step(self):
        self.check()
        self.transitions += 1
        if self.limit is not None and self.transitions > self.limit:
            raise FilterLimit('shared mask-transition budget exhausted')


class FilteredAtlas:
    def __init__(self, compilation, **preparation):
        self.compilation = compilation
        self.intrinsic = IntrinsicPrepared(compilation.blocks, **preparation)

    def solve(self, objective, *, zeros=(), excluded=(), budget=None):
        """Positive source-vector query with downward-closed support exclusions.

        A complete negative concerns this linear query only. Support descent
        is performed by search(), not here. Preparation and linear algebra are
        outside the mask-transition cap; cancellation callbacks still run.
        """
        budget = Budget(None, lambda: None) if budget is None else budget
        budget.check()
        co = self.compilation
        costs, master, zz = co.query(objective, zeros)
        zz = tuple(frozenset(z) for z in zz)
        clauses = tuple(frozenset(s) for s in excluded)
        if any(any(type(j) is not int or not 0 <= j < co.source.n for j in s) for s in clauses):
            raise ValueError('invalid excluded source support')
        if any(not s for s in clauses):
            return dict(status='NO_POSITIVE', vectors=None, port=None, value=None)
        p = self.intrinsic.prepared
        master = self.intrinsic.reduction.reduce_master(master)
        full = (1 << len(clauses))-1
        needed = tuple(tuple(frozenset(k for k,j in enumerate(ids) if j in s) for s in clauses)
                       for ids in co.local_to_source)

        def mask(i, support):
            return sum(1 << k for k, local in enumerate(needed[i]) if local-support)

        empty = tuple(mask(i, frozenset()) for i in range(len(p.blocks)))
        for i, rays in enumerate(p.zero_rays):
            other = 0
            for k, m in enumerate(empty):
                if k != i:
                    other |= m
            for r in rays:
                budget.check()
                support = frozenset(j for j,x in enumerate(r) if x)
                if support & zz[i] or (other | mask(i, support)) != full:
                    continue
                value = dot(costs[i], r)
                if value > 0:
                    vectors = [(Q(0),)*b.n for b in p.blocks]
                    vectors[i] = tuple(map(Q, r))
                    return dict(status='POSITIVE', kind='zero-port', vectors=tuple(vectors),
                        port=self.intrinsic.reduction.lift_port((Q(0),)*p.d), value=value)
        rewards = tuple(tuple(dot(c,r.vector) for r in rays) for c,rays in zip(costs,p.rays))
        best = None
        max_states = 1
        for t, y in enumerate(p.vertices):
            budget.check()
            states = {0:(dot(master, y), ())}
            for i in range(len(p.blocks)):
                choices = {}
                for ids, weights, support in p.tables[i][t]:
                    budget.check()
                    if support & zz[i]:
                        continue
                    m = mask(i, support)
                    score = sum((w*rewards[i][j] for j,w in zip(ids, weights)), Q(0))
                    if m not in choices or score > choices[m][0]:
                        choices[m] = (score, ids, weights)
                updated = {}
                for prior, (score, path) in states.items():
                    for m, (local, ids, weights) in choices.items():
                        budget.step()
                        total, combined = score+local, prior | m
                        if combined not in updated or total > updated[combined][0]:
                            updated[combined] = (total, path+((ids, weights),))
                states = updated
                max_states = max(max_states, len(states))
                if not states:
                    break
            if full in states and (best is None or states[full][0] > best[0]):
                best = (states[full][0], t, states[full][1])
        if best is None:
            return dict(status='NO_POSITIVE', vectors=None, port=None, value=None, max_states=max_states)
        value, t, path = best
        vectors = tuple(tuple(sum((w*rays[j].vector[k] for j,w in zip(ids, weights)), Q(0))
                              for k in range(b.n))
                        for b,rays,(ids,weights) in zip(p.blocks,p.rays,path))
        return dict(status='POSITIVE' if value>0 else 'NO_POSITIVE', vectors=vectors,
                    port=self.intrinsic.reduction.lift_port(p.vertices[t]), value=value,
                    max_states=max_states, kind='atlas')

    def search(self, objective, inspect, *, zeros=(), max_rejected=16,
               max_transitions=1000000, check=lambda: None):
        """Find an accepted positive extreme ray, or exhaust all such rays.

        inspect(x) returns a mapping with a strict boolean `accepted` field and
        any caller evidence. Acceptance is the caller's verified predicate.
        Negative completion excludes accepted *extreme rays* in this source
        and face; it makes no general knot or manifold claim.
        """
        if max_rejected is not None and (type(max_rejected) is not int or max_rejected<0):
            raise ValueError('max_rejected must be a nonnegative integer or None')
        budget = Budget(max_transitions, check)
        rejected, trace = [], []
        queries = 0
        objective = tuple(rational(x) for x in objective)
        zeros = tuple(zeros)
        co = self.compilation
        try:
            while True:
                queries += 1
                answer = self.solve(objective, zeros=zeros, excluded=rejected, budget=budget)
                if answer['status'] == 'NO_POSITIVE':
                    return dict(status='NO_ACCEPTED_EXTREME', rejected=rejected, trace=trace,
                                queries=queries, transitions=budget.transitions)
                x = co.reconstruct(answer['vectors'])
                witness = extreme_witness(co.source, x, objective, check=budget.check)
                coordinates = witness['coordinates']
                budget.check()
                if not verify_vector(co.source.n, co.source.equations, co.source.conflicts,
                        objective, coordinates, zeros=zeros, extreme=True):
                    raise ArithmeticError('independent source extremality replay failed')
                support = frozenset(j for j,v in enumerate(coordinates) if v)
                if any(s <= support for s in rejected):
                    raise ArithmeticError('support descent violated an exclusion')
                try:
                    evidence = inspect(coordinates)
                except BaseException:
                    budget.callback_failed = True
                    raise
                if type(evidence) is not dict or type(evidence.get('accepted')) is not bool:
                    raise ValueError('inspect must return a dict with boolean accepted')
                trace.append(dict(coordinates=coordinates, evidence=evidence,
                                  max_states=answer.get('max_states', 1)))
                if evidence['accepted']:
                    return dict(status='ACCEPTED_EXTREME', coordinates=coordinates, trace=trace,
                                rejected=rejected, queries=queries, transitions=budget.transitions)
                if max_rejected is not None and len(rejected) >= max_rejected:
                    raise FilterLimit('rejected-support budget exhausted')
                rejected.append(support)
        except FilterLimit as exc:
            if budget.callback_failed:
                raise
            return dict(status='INCONCLUSIVE', reason=str(exc), rejected=rejected,
                        trace=trace, queries=queries, transitions=budget.transitions)
