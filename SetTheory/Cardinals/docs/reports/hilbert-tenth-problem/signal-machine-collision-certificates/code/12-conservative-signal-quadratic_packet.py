"""Exact finite event-branch compiler and canonical quadratic packet.

Only the small demonstration is fully enumerated by default. The generator
supports an arbitrary finite rational/integer-speed table after integer speed
normalization, but all modes of the literal 114-label, 18-signal machine are
far too numerous for a routine replay. No unbounded-history compression occurs.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import lcm
from pathlib import Path
import json

def exact_vector(values, dimension=None, *, natural=False):
    values=tuple(values)
    if (dimension is not None and len(values)!=dimension
        or any(type(v) is not int or natural and v<0 for v in values)):
        raise ValueError('Expected exact integer vector of the declared dimension')
    return values


def packet_interface(branches, x, y):
    branches=tuple(branches);x=exact_vector(x,natural=True)
    y=exact_vector(y,len(x),natural=True)
    if not x or any(type(b) is not Branch or len(b.matrix)!=len(x) for b in branches):
        raise ValueError('Branch and endpoint dimensions must agree and be positive')
    return branches,x,y


@dataclass(frozen=True)
class Guard:
    kind: str                     # eq, gt, ge
    coeff: tuple[int, ...]
    def __post_init__(self):
        if self.kind not in ('eq','gt','ge'):
            raise ValueError('Unknown guard kind')
        object.__setattr__(self,'coeff',exact_vector(self.coeff))
    def value(self, x):
        x=exact_vector(x,len(self.coeff))
        return sum(a*b for a,b in zip(self.coeff, x))
    def holds(self, x):
        z=self.value(x)
        return z==0 if self.kind=='eq' else z>0 if self.kind=='gt' else z>=0

@dataclass(frozen=True)
class Branch:
    matrix: tuple[tuple[int,...],...]
    guards: tuple[Guard,...]
    mode: tuple[str,...]=()
    tied_edges: tuple[int,...]=()
    def __post_init__(self):
        matrix=tuple(tuple(row) for row in self.matrix);d=len(matrix)
        if d<1:raise ValueError('Branch dimension must be positive')
        matrix=tuple(exact_vector(row,d) for row in matrix)
        guards=tuple(self.guards)
        if any(type(g) is not Guard or len(g.coeff)!=d for g in guards):
            raise ValueError('Guard dimension must match the matrix')
        object.__setattr__(self,'matrix',matrix)
        object.__setattr__(self,'guards',guards)
        object.__setattr__(self,'mode',tuple(self.mode))
        object.__setattr__(self,'tied_edges',tuple(self.tied_edges))
    def output(self, x):
        x=exact_vector(x,len(self.matrix))
        return tuple(sum(a*b for a,b in zip(row,x)) for row in self.matrix)
    def holds(self, x):
        x=exact_vector(x,len(self.matrix),natural=True)
        return all(g.holds(x) for g in self.guards)


def mode_code(labels, alphabet):
    """One plus the zero-based base-|alphabet| lexicographic word index."""
    ids={a:i for i,a in enumerate(alphabet)}
    q=0
    for a in labels:q=q*len(alphabet)+ids[a]
    return q+1


def event_mode_branches(mode, speeds, rules, *, scaling='pivot'):
    """Generate all candidate legal-rule branches of one ordered label mode.

    Guards, rather than numerical sampling, decide geometric feasibility.
    scaling='pivot' uses c_j I - c e_j^T; 'global' uses D times the rational
    projection. Rows/columns are gaps followed by the mode coordinate.
    """
    alphabet=tuple(sorted(speeds));n=len(mode);d=n
    c=tuple(speeds[mode[i]]-speeds[mode[i+1]] for i in range(n-1))
    closing=tuple(i for i,x in enumerate(c) if x>0)
    D=lcm(*(abs(a-b) for a in speeds.values() for b in speeds.values() if a!=b)) if len(set(speeds.values()))>1 else 1
    q=mode_code(mode,alphabet)
    for bits in product((0,1),repeat=len(closing)):
        J=tuple(i for i,b in zip(closing,bits) if b)
        if not J:continue
        j=J[0];S=set(J);out=[];start=0;valid=True
        for k in range(n):
            if k==n-1 or k not in S:
                block=mode[start:k+1]
                if len(block)>1:
                    key=frozenset(block)
                    if key not in rules or len(key)!=len(block):valid=False;break
                    new=rules[key]
                    if len(new)!=len(block):raise ValueError('Rules must preserve block cardinality')
                    if len({speeds[a] for a in new})!=len(new):raise ValueError('Output speeds must be distinct')
                    out.extend(sorted(new,key=speeds.__getitem__))
                else:out.extend(block)
                start=k+1
        if not valid:continue
        scale=c[j] if scaling=='pivot' else D if scaling=='global' else None
        if scale is None:raise ValueError(scaling)
        assert scale%c[j]==0
        M=[[scale*int(i==k)-(scale//c[j])*c[i]*int(k==j) for k in range(n-1)] for i in range(n-1)]
        qp=mode_code(out,alphabet)
        matrix=tuple(tuple(row)+(0,) for row in M)+(tuple(qp*sum(M[i][k] for i in range(n-1)) for k in range(n-1))+(0,),)
        guards=[Guard('eq',(-q,)*(n-1)+(1,)),Guard('gt',(1,)*(n-1)+(0,))]
        for i in range(n-1):
            if c[i]>=0:guards.append(Guard('gt',tuple(int(k==i) for k in range(n))))
        guards.append(Guard('gt',tuple(int(k==j) for k in range(n))))
        for i in range(n-1):
            if i==j:continue
            row=tuple(c[j]*int(k==i)-c[i]*int(k==j) for k in range(n))
            guards.append(Guard('eq' if i in S else 'gt',row))
        yield Branch(matrix,tuple(guards),tuple(mode),J)


def all_event_branches(speeds,rules,n,*,scaling='pivot'):
    """Lazy complete finite enumerator; enormous for universal instances."""
    assert n>=2 and speeds
    assert all(isinstance(v,int) for v in speeds.values())
    for incoming,outgoing in rules.items():
        assert len(incoming)==len(outgoing)>=2
        assert len({speeds[a] for a in incoming})==len(incoming)
        assert len({speeds[a] for a in outgoing})==len(outgoing)
    for mode in product(sorted(speeds),repeat=n):
        yield from event_mode_branches(mode,speeds,rules,scaling=scaling)


def ledger(branches,d):
    kinds=[g.kind for b in branches for g in b.guards]
    E,T,W=(kinds.count(k) for k in ('eq','gt','ge'));B=len(branches)
    return dict(dimension=d,branches=B,equality_guards=E,strict_guards=T,weak_guards=W,
                auxiliary_variables=B*(d+1)+T+W,
                squared_affine_residuals=1+2*d+E+T+W,quadratic_products=B)


def canonical_witness(branches,x,y):
    branches,x,y=packet_interface(branches,x,y)
    active=[r for r,b in enumerate(branches) if b.holds(x)]
    if len(active)>1:raise ValueError('Branch guards are not disjoint')
    if not active or branches[active[0]].output(x)!=tuple(y):return None
    a=active[0];d=len(x)
    selectors=tuple(int(r==a) for r in range(len(branches)))
    copies=tuple(tuple(x) if r==a else (0,)*d for r in range(len(branches)))
    slacks=tuple(tuple(g.value(copies[r])-selectors[r]*int(g.kind=='gt')
                       for g in b.guards if g.kind!='eq') for r,b in enumerate(branches))
    assert all(v>=0 for row in slacks for v in row)
    return selectors,copies,slacks


def packet_terms(branches,x,y,witness):
    """Return every affine residual and every complementarity product."""
    branches,x,y=packet_interface(branches,x,y)
    selectors,copies,slacks=witness;d=len(x);B=len(branches)
    selectors=exact_vector(selectors,B,natural=True)
    copies=tuple(exact_vector(z,d,natural=True) for z in copies)
    slacks=tuple(tuple(row) for row in slacks)
    if len(copies)!=B or len(slacks)!=B:
        raise ValueError('One copy and slack row required per branch')
    slacks=tuple(exact_vector(row,sum(g.kind!='eq' for g in b.guards),natural=True)
                 for row,b in zip(slacks,branches))
    residuals=[sum(selectors)-1]
    residuals.extend(x[i]-sum(z[i] for z in copies) for i in range(d))
    residuals.extend(y[i]-sum(branches[r].output(copies[r])[i] for r in range(B)) for i in range(d))
    for r,b in enumerate(branches):
        it=iter(slacks[r])
        for g in b.guards:
            v=g.value(copies[r])
            if g.kind!='eq':
                s=next(it);assert isinstance(s,int) and s>=0
                v-=s+selectors[r]*int(g.kind=='gt')
            residuals.append(v)
        assert next(it,None) is None
    products=tuple((sum(selectors)-selectors[r])*sum(copies[r]) for r in range(B))
    assert all(z>=0 for z in products)
    return tuple(residuals),products


def polynomial_value(branches,x,y,witness):
    rows,terms=packet_terms(branches,x,y,witness)
    return sum(z*z for z in rows)+sum(terms)


def main():
    import conservative_signal as cs
    speeds={'a':2,'b':0,'c':-2}
    rules={frozenset(z):frozenset(z) for bits in product((0,1),repeat=3)
           if len(z:=[a for a,b in zip(speeds,bits) if b])>=2}
    results={}
    for scaling in ('pivot','global'):
        branches=tuple(all_event_branches(speeds,rules,3,scaling=scaling))
        L=ledger(branches,3);tested=legal=ties=0
        for mode in product(sorted(speeds),repeat=3):
            for gap in product(range(3),repeat=2):
                if sum(gap)==0:continue
                if any(g==0 and speeds[mode[i]]>=speeds[mode[i+1]] for i,g in enumerate(gap)):continue
                conf=[(Fraction(0),mode[0]),(Fraction(gap[0]),mode[1]),(Fraction(sum(gap)),mode[2])]
                out=cs.event(conf,{a:Fraction(v) for a,v in speeds.items()},rules)
                x=gap+(mode_code(mode,tuple(sorted(speeds)))*sum(gap),)
                chosen=[b for b in branches if b.holds(x)]
                assert len(chosen)==int(out is not None)
                tested+=1
                if out is None:continue
                new,dt,rec=out;j=rec['pivot'];factor=(speeds[mode[j]]-speeds[mode[j+1]]) if scaling=='pivot' else rec['D']
                h=tuple(int(factor*(new[i+1][0]-new[i][0])) for i in range(2))
                q=mode_code(tuple(a for _,a in new),tuple(sorted(speeds)))
                y=h+(q*sum(h),)
                w=canonical_witness(branches,x,y);assert w is not None
                rows,terms=packet_terms(branches,x,y,w)
                assert len(rows)==L['squared_affine_residuals'] and len(terms)==L['quadratic_products']
                assert polynomial_value(branches,x,y,w)==0
                assert canonical_witness(branches,x,(y[0]+1,)+y[1:]) is None
                legal+=1;ties+=len(rec['J'])>1
        results[scaling]=dict(**L,tested_germs=tested,legal_steps=legal,simultaneous_steps=ties,
                             canonical_residuals_all_zero=True)
    output=Path(__file__).resolve().parent.parent/'receipts'/'QUADRATIC_PACKET_RESULTS.json'
    output.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
