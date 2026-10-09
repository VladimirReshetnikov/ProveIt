"""Independent unreduced F2 cube oracle with strict dots and reverse saddles.
Does NOT import the scanner. Exponential; intended only for finite audits.
"""
from __future__ import annotations
from collections import defaultdict
from .diagram import DSU, validate
from .binary import apply, rank
from .dots import monomials, validate as validate_polynomial

class Cube:
    def __init__(self, pd, *, max_crossings=10, max_dimension=200000):
        self.pd = validate(pd)
        n = len(pd)
        if n > max_crossings: raise ValueError('independent cube crossing ceiling')
        if not n:
            self.states = [((), {0:0})]
            self.basis = [(0,0),(0,1)]; self.index = {(0,0):0,(0,1):1}
            self.dimension = 2; self.d = (0,0); self.nu = (0,1)
            self.degrees = (0,0); self.labels = [0]
            return
        labels = sorted({x for c in pd for x in c}); self.labels = labels
        states = []
        for s in range(1 << n):
            ds = DSU(labels)
            for j,(a,b,c,d) in enumerate(pd):
                for u,v in (((a,d),(b,c)) if (s>>j)&1 else ((a,b),(c,d))): ds.union(u,v)
            roots = sorted({ds.find(x) for x in labels})
            ri = {r:i for i,r in enumerate(roots)}
            owner = {x:ri[ds.find(x)] for x in labels}
            comps = tuple(frozenset(x for x in labels if owner[x]==j) for j in range(len(roots)))
            states.append((comps,owner))
        dim = sum(1 << len(c) for c,_ in states)
        if dim > max_dimension: raise ValueError('independent cube dimension ceiling')
        basis = [(s, dots) for s,(c,_) in enumerate(states) for dots in range(1<<len(c))]
        self.states, self.basis = states,basis
        self.index = {v:j for j,v in enumerate(basis)}; self.dimension = dim
        self.degrees = tuple(s.bit_count() for s,_ in basis)
        self.d = tuple(self._d_column(s,dots) for s,dots in basis)
        nu = []
        for s,dots in basis:
            col,t = 0,dots
            while t:
                low = t & -t; t ^= low
                col ^= 1 << self.index[s,dots ^ low]
            nu.append(col)
        self.nu = tuple(nu)

    def saddle(self, s, t, crossing, dots):
        old,own = self.states[s]; new,no = self.states[t]
        ao = {own[a] for a in self.pd[crossing]}; an = {no[a] for a in self.pd[crossing]}
        base = 0
        for i,comp in enumerate(old):
            if i not in ao and (dots>>i)&1: base |= 1 << no[next(iter(comp))]
        if len(new) == len(old)-1:
            if len(ao)!=2 or len(an)!=1: raise ArithmeticError('bad merge')
            cnt = sum((dots>>i)&1 for i in ao)
            outputs = [] if cnt==2 else [base | ((1 << next(iter(an))) if cnt else 0)]
        elif len(new) == len(old)+1:
            if len(ao)!=1 or len(an)!=2: raise ArithmeticError('bad split')
            a,b = sorted(an)
            outputs = [base|(1<<a)|(1<<b)] if (dots>>next(iter(ao)))&1 else [base|(1<<a),base|(1<<b)]
        else: raise ArithmeticError('nonclassical saddle')
        col = 0
        for val in outputs: col ^= 1 << self.index[t,val]
        return col

    def _d_column(self,s,dots):
        col = 0
        for j in range(len(self.pd)):
            if not (s>>j)&1: col ^= self.saddle(s,s|(1<<j),j,dots)
        return col

    def reverse(self,crossing):
        if not 0 <= crossing < len(self.pd): raise ValueError('crossing out of range')
        return tuple(self.saddle(s,s^(1<<crossing),crossing,dots) if (s>>crossing)&1 else 0
                     for s,dots in self.basis)

    def polynomial(self,theta,marks):
        marks = list(marks); validate_polynomial(theta,len(marks))
        if any(m not in self.labels for m in marks): raise ValueError('mark is not a diagram edge')
        mons = list(monomials(theta)); columns=[]
        for s,dots in self.basis:
            own=self.states[s][1]; col=0
            for mon in mons:
                value=dots
                while mon:
                    low=mon & -mon; mon ^= low
                    bit=1 << own[marks[low.bit_length()-1]]
                    if value & bit: break
                    value |= bit
                else: col ^= 1 << self.index[s,value]
            columns.append(col)
        return tuple(columns)

    def homology_rank(self): return self.dimension-2*rank(self.d)

    def check(self):
        if any(apply(self.d,c) for c in self.d): raise ArithmeticError('d squared is nonzero')
        return True

def quiver_columns(d,theta,dimensions,arrows):
    """Matrix of d_C + theta B; B^2 need not vanish."""
    D=len(d); offsets=[]; total=0
    for n in dimensions: offsets.append(total); total+=n
    cols=[]
    for h,n in enumerate(dimensions):
        for j in range(n):
            copy=offsets[h]+j
            arrow=arrows[h][j] if h<len(arrows) else 0
            for x in range(D):
                col=d[x] << (D*copy); a=arrow
                while a:
                    low=a & -a; a ^= low
                    target=offsets[h+1]+low.bit_length()-1
                    col ^= theta[x] << (D*target)
                cols.append(col)
    return tuple(cols)

def quiver_rank(cube,theta,dimensions,arrows, *, check=False):
    cols=quiver_columns(cube.d,theta,dimensions,arrows)
    if check and any(apply(cols,c) for c in cols): raise ArithmeticError('tensor d squared')
    return len(cols)-2*rank(cols)

def interval_rank(cube,theta,length,*,check=False):
    if type(length) is not int or length<1: raise ValueError('length must be positive')
    return quiver_rank(cube,theta,[1]*length,[(1,)]*(length-1),check=check)
