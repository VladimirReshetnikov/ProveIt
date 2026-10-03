#!/usr/bin/env python3
"""Two orthant-exact upgrades of the audited binary finite-prism cubic.

Only imports the locally authored, approved coefficient packet, never upstream
ProveIt code. See PROOF.md for the all-real theorem and semantic boundaries.
"""
from pathlib import Path
import hashlib, importlib.util, itertools, sys
BASE_PATH=Path(__file__).resolve().parent/'approved_base'/'prism_certificate.py'
BASE_SHA256=hashlib.sha256(BASE_PATH.read_bytes()).hexdigest()
EXPECTED_BASE_SHA256='bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2'
if BASE_SHA256!=EXPECTED_BASE_SHA256:raise RuntimeError('approved base compiler changed')
spec=importlib.util.spec_from_file_location('_real_certificate_base', BASE_PATH)
base=importlib.util.module_from_spec(spec);sys.modules[spec.name]=base
_old_dont_write_bytecode=sys.dont_write_bytecode
try:
    sys.dont_write_bytecode=True
    spec.loader.exec_module(base)
finally:sys.dont_write_bytecode=_old_dont_write_bytecode
Prism=base.Prism
PeriodicInput=base.PeriodicInput

class RealCompiler(base.Compiler):
    """variant='merged': replace fg by f(g+k+c); 'flat': add f(k+c); 'sharp': all pairs."""
    def __init__(self,P,source,variant='merged'):
        if variant not in ('merged','sharp','flat'):raise ValueError('unknown variant')
        self.variant=variant
        super().__init__(P,source)
    def vertex_summands(self,p):
        for t in super().vertex_summands(p):
            if self.variant=='merged' and t.label.endswith('.inactive_g'):
                yield base.Summand(t.label,'product',t.residual,base.combine(t.weight,self.u(p)))
            else:yield t
        i=self.P.index(p)
        if self.variant=='merged':return
        if self.variant=='flat':
            yield base.Summand(f'v{i}.binary_support','product',base.var(self.v(p,'f')),self.u(p))
        else:
            for a,b in itertools.combinations(('f','k','c'),2):
                yield base.Summand(f'v{i}.onehot_{a}_{b}','product',base.var(self.v(p,a)),base.var(self.v(p,b)))
    def edge_summands(self,p,q):
        yield from super().edge_summands(p,q)
        if self.variant=='sharp':
            i=self.P.edge_index(p,q)
            for a,b in itertools.combinations(base.EDGE_FIELDS[:5],2):
                yield base.Summand(f'e{i}.onehot_{a}_{b}','product',base.var(self.ev(p,q,a)),base.var(self.ev(p,q,b)))
    def evaluate_orthant(self,w):
        """Exact on int/Fraction inputs; accepts other ordered scalar types.

        Does not reinterpret small floating values as zero or prove zero by a
        numerical tolerance. The inherited evaluate() keeps its natural API.
        """
        if len(w)!=self.P.witnesses:raise ValueError('wrong witness count')
        if any(x<0 for x in w):raise ValueError('outside nonnegative orthant')
        return sum(t.value(w) for t in self.summands())
    def closed_ledger(self):
        out=super().closed_ledger();V,E=self.P.V,self.P.E
        if self.variant=='sharp':
            n=3*V+10*E
            delta={'summands':n,'product_summands':n,'records':n,'evaluation_mults':3*n,'evaluation_adds':n,'expansion_coefficient_mults':n}
        elif self.variant=='merged':
            delta={'records':2*V,'evaluation_mults':2*V,'evaluation_adds':2*V,'expansion_coefficient_mults':2*V}
        else:
            delta={'summands':V,'product_summands':V,'records':2*V,'evaluation_mults':4*V,'evaluation_adds':2*V,'expansion_coefficient_mults':2*V}
        for k,v in delta.items():out[k]+=v
        return out
    def penalty_monomials(self):
        for p in self.P.points():
            for a,b in (('f','k'),('f','c')):
                yield tuple(sorted((self.v(p,a),self.v(p,b))))
            if self.variant=='sharp':yield tuple(sorted((self.v(p,'k'),self.v(p,'c'))))
        if self.variant=='sharp':
            for p,q in self.P.edges():
                for a,b in itertools.combinations(base.EDGE_FIELDS[:5],2):
                    yield tuple(sorted((self.ev(p,q,a),self.ev(p,q,b))))
