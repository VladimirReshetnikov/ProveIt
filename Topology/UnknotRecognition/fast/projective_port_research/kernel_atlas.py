"""Research atlas with reusable local and independently checked source kernels.

The atlas construction below adapts the MIT-0 report 113 Prepared constructor;
its preserved source remains unchanged. The support-filtered search adapts the
maintained filtered.py algorithm. All enumeration, masking and geometric
predicate contracts are unchanged; only exact linear algebra is replaced.
This module is not imported by the default recognizer.
"""
from itertools import combinations

from .common import (Block, Prepared, IntrinsicPrepared, PortBlock,
                     compress_common_ports)
from .filtered import FilteredAtlas, Budget, FilterLimit
from .kernel_rays import enumerate_rays_kernel
from projective_ports.atlas import Ray, Simplex, projective_atlas
from projective_ports.exact import Q, rational, nullspace, solve_unique
from fastunknot.source_kernel import SourceKernel
from fastunknot.source_kernel_verify import SourceKernelVerifier


class KernelPrepared(Prepared):
    """The same complete atlas, using deduplicated kernel hyperplanes."""
    def __init__(self, blocks, *, max_supports=None, max_candidates=None,
                 check=lambda:None):
        self.blocks=tuple(blocks)
        if not self.blocks or len({b.d for b in self.blocks})!=1:
            raise ValueError('nonempty blocks must have identical port dimension')
        self.d=self.blocks[0].d
        self.local_kernel_stats = []
        raw_rays = []
        for b in self.blocks:
            statistics = {}
            raw_rays.append(enumerate_rays_kernel(b, max_supports=max_supports,
                                                 check=check, stats=statistics))
            self.local_kernel_stats.append(statistics)
        self.raw_rays = tuple(raw_rays)
        zero=[]; rays=[]; simplices=[]
        for b,raw in zip(self.blocks,self.raw_rays):
            zr=[]; rr=[]
            for r in raw:
                image=b.image(r); h=sum(image,Q(0)); support=frozenset(j for j,v in enumerate(r) if v)
                if not h:
                    zr.append(r)
                else:
                    rr.append(Ray(r,support,tuple(v/h for v in image),tuple(Q(v)/h for v in r)))
            ss=[]
            for k in range(1,min(self.d,len(rr))+1):
                for ids in combinations(range(len(rr)),k):
                    check()
                    support=frozenset().union(*(rr[j].support for j in ids))
                    if not b.compatible_support(support): continue
                    cols=tuple(tuple(rr[j].port[h] for j in ids) for h in range(self.d))
                    # Independence of normalized port columns is affine independence.
                    if nullspace(cols,k): continue
                    ss.append(Simplex(ids,support))
            zero.append(tuple(zr)); rays.append(tuple(rr)); simplices.append(tuple(ss))
        self.zero_rays=tuple(zero); self.rays=tuple(rays); self.simplices=tuple(simplices)
        self.vertices,self.stats=projective_atlas(
            [tuple(r.port for r in rr) for rr in self.rays],self.d,
            max_candidates=max_candidates,check=check)
        self.stats=dict(self.stats, rays=sum(map(len,self.raw_rays)),
                        nonzero_port_rays=sum(map(len,self.rays)),
                        simplices=sum(map(len,self.simplices)), vertices=len(self.vertices))
        # Store all feasible barycentric mixtures at atlas vertices. This cache
        # is independent of objectives and zero-face restrictions.
        tables=[]
        for rr,ss in zip(self.rays,self.simplices):
            table=[]
            for y in self.vertices:
                choices=[]
                for simplex in ss:
                    check()
                    cols=tuple(tuple(rr[j].port[h] for j in simplex.rays) for h in range(self.d))
                    w=solve_unique(cols,y,len(simplex.rays))
                    if w is not None and all(a>=0 for a in w):
                        # Zero coefficients must not exclude a valid anchor.
                        actual=frozenset().union(*(rr[j].support for j,a in zip(simplex.rays,w) if a))
                        choices.append((simplex.rays,w,actual))
                table.append(tuple(choices))
            tables.append(tuple(table))
        self.tables=tuple(tables)


class KernelIntrinsicPrepared(IntrinsicPrepared):
    def __init__(self, blocks, **kwargs):
        self.original = tuple(blocks)
        self.reduction = compress_common_ports(
            tuple(PortBlock(b.n, b.equations, b.ports, b.conflicts)
                  for b in self.original), check=kwargs.get('check', lambda: None))
        self.prepared = KernelPrepared(tuple(Block(b.n, b.equations, b.ports, b.conflicts)
                                             for b in self.reduction.blocks), **kwargs)


class KernelFilteredAtlas(FilteredAtlas):
    """Reuse one producer chart and one independent checker across all queries."""
    def __init__(self, compilation, **preparation):
        self.compilation = compilation
        self.intrinsic = KernelIntrinsicPrepared(compilation.blocks, **preparation)
        check = preparation.get('check', lambda: None)
        self.source_kernel = SourceKernel(compilation.source, check=check)
        self.source_verifier = SourceKernelVerifier(compilation.source, check=check)

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
                witness = self.source_kernel.extreme_witness(
                    x, objective, zeros=zeros, check=budget.check)
                coordinates = witness['coordinates']
                budget.check()
                if not self.source_verifier.verify(coordinates, objective,
                        zeros=zeros, check=budget.check):
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
