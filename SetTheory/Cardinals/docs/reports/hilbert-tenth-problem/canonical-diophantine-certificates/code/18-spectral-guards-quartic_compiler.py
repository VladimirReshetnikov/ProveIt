"""An executable quadratic-residual / exponential-atom certificate compiler.

Every numeric variable is nonnegative. Inputs are distinguished from witnesses.
The ordinary polynomial is represented exactly as sum(residual**2), without
expanding the outer sum. In primitive-power mode it is a quasi-Diophantine
system, NOT an ordinary polynomial. In bounded-power mode every residual has
degree <= 2, so the sum has degree <= 4.
"""
from __future__ import annotations
import json
from dataclasses import dataclass
from math import comb
from pathlib import Path
from spectral_guards import decode_certificate

class Poly:
    def __init__(self, terms=None):
        self.terms = {k: v for k, v in (terms or {}).items() if v}
    @staticmethod
    def as_poly(x):
        return x if isinstance(x, Poly) else Poly({(): int(x)})
    def __add__(self, other):
        out = dict(self.terms)
        for k, v in self.as_poly(other).terms.items():
            out[k] = out.get(k, 0)+v
        return Poly(out)
    __radd__ = __add__
    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})
    def __sub__(self, other):
        return self + (-self.as_poly(other))
    def __rsub__(self, other):
        return self.as_poly(other) - self
    def __mul__(self, other):
        out = {}
        for k, v in self.terms.items():
            for l, w in self.as_poly(other).terms.items():
                key = tuple(sorted(k+l))
                out[key] = out.get(key, 0)+v*w
        return Poly(out)
    __rmul__ = __mul__
    def evaluate(self, values):
        total = 0
        for key, coefficient in self.terms.items():
            term = coefficient
            for i in key:
                term *= values[i]
            total += term
        return total
    @property
    def degree(self):
        return max(map(len, self.terms), default=0)
    @property
    def index(self):
        if len(self.terms) != 1:
            raise ValueError("Not a single variable")
        (key, coefficient), = self.terms.items()
        if len(key) != 1 or coefficient != 1:
            raise ValueError("Not a single variable")
        return key[0]

@dataclass
class Signed:
    plus: Poly
    minus: Poly
    @property
    def expr(self):
        return self.plus-self.minus

class Emitter:
    def __init__(self, bits: int | None):
        if bits is not None and bits < 1:
            raise ValueError("bits must be at least 1")
        self.bits = bits
        self.names = []
        self.values = []
        self.inputs = []
        self.residuals = []
        self.power_atoms = []
        self.square_cache = {}
        self.bits_cache = {}
        self.power_cache = {}
    def new(self, name, value, is_input=False):
        if not isinstance(value, int) or value < 0:
            raise ValueError(f"Negative or nonintegral natural: {name}")
        index = len(self.values)
        self.names.append(f"{name}_{index}")
        self.values.append(value)
        if is_input:
            self.inputs.append(index)
        return Poly({(index,): 1})
    def val(self, expr):
        return Poly.as_poly(expr).evaluate(self.values)
    def require(self, expr):
        expr = Poly.as_poly(expr)
        if expr.degree > 2:
            raise ValueError("Residual of degree greater than two")
        if expr.terms:
            self.residuals.append(expr)
    def nat(self, name, expr):
        v = self.new(name, self.val(expr))
        self.require(v-expr)
        return v
    def boolean(self, name, value):
        b = self.new(name, int(value))
        self.require(b*(b-1))
        return b
    def signed(self, name, expr):
        value = self.val(expr)
        p = self.new(name+"p", max(value, 0))
        n = self.new(name+"n", max(-value, 0))
        self.require(p-n-expr)
        self.require(p*n)
        return Signed(p, n)
    def sign_bits(self, expr):
        value = self.val(expr)
        p = self.new("positive", int(value > 0))
        z = self.new("zero", int(value == 0))
        n = self.new("negative", int(value < 0))
        a = self.new("positive_slack", max(value-1, 0))
        b = self.new("negative_slack", max(-value-1, 0))
        self.require(p+z+n-1)
        self.require(expr-p*(1+a)+n*(1+b))
        self.require((1-p)*a)
        self.require((1-n)*b)
        return (p,z,n)
    def le(self, a, b):
        p,z,n = self.sign_bits(b-a)
        return self.nat("le", p+z)
    def minmax(self, a, b):
        le = self.le(a,b)
        lo = self.nat("minimum", le*a+(1-le)*b)
        hi = self.nat("maximum", le*b+(1-le)*a)
        return lo,hi
    def power(self, base, exponent):
        key=(base.index, exponent.index)
        if key in self.power_cache:
            return self.power_cache[key]
        if self.bits is None:
            result = self.new("power", pow(self.val(base), self.val(exponent)))
            self.power_atoms.append((base.index, exponent.index, result.index))
        else:
            B = self.bits
            e = self.val(exponent)
            if not 0 <= e < 2**B:
                raise ValueError("Exponent exceeds the declared bit bound")
            if exponent.index not in self.bits_cache:
                bs=[self.boolean("exponent_bit", (e>>i)&1) for i in range(B)]
                self.require(exponent-sum((2**i)*x for i,x in enumerate(bs)))
                self.bits_cache[exponent.index]=bs
            bs=self.bits_cache[exponent.index]
            if base.index not in self.square_cache:
                squares=[base]
                for i in range(1,B):
                    squares.append(self.nat("base_square", squares[-1]*squares[-1]))
                self.square_cache[base.index]=squares
            squares=self.square_cache[base.index]
            product=Poly.as_poly(1)
            for bit,square in zip(bs,squares):
                factor=self.nat("power_factor", 1+bit*(square-1))
                product=self.nat("power_product", product*factor)
            result=product
        self.power_cache[key]=result
        return result
    def failed_residuals(self):
        return [i for i,p in enumerate(self.residuals) if p.evaluate(self.values)]
    def summary(self):
        return {"variables":len(self.values), "inputs":len(self.inputs),
                "witnesses":len(self.values)-len(self.inputs),
                "quadratic_residuals":len(self.residuals),
                "max_residual_degree":max((p.degree for p in self.residuals),default=0),
                "power_atoms":len(self.power_atoms),
                "failed_residuals":len(self.failed_residuals()),
                "largest_value_bits":max(map(int.bit_length,self.values),default=0),
                "polynomial_degree_bound":4 if not self.power_atoms else None}
    def export(self,path):
        data={"format":"spectral-guards-residuals-v1", "bits":self.bits,
              "polynomial":"sum of squares of listed residuals" if not self.power_atoms
                           else "quasi-Diophantine: quadratic equations plus power atoms",
              "names":self.names, "values":self.values, "inputs":self.inputs,
              "residuals":[[[c,list(k)] for k,c in sorted(p.terms.items())]
                           for p in self.residuals],
              "power_atoms":[list(a) for a in self.power_atoms],
              "summary":self.summary()}
        Path(path).write_text(json.dumps(data,indent=2)+"\n")


def compile_certificate(certificate: dict, bits: int | None,
                        require_nonnegative: bool=False) -> Emitter:
    """Emit a fixed-shape system and the assignment from a candidate chart.

    The polynomial structure depends only on shape, bit bound, and requested
    predicate, not on data or chart contents. A malformed partition can give
    an invalid natural slack; valid-shaped false sign claims are emitted and
    rejected by nonzero residuals. This is an exporter, not a Diophantine solver.
    """
    seq,T,charts=decode_certificate(certificate)
    if T<0 or seq.dimension<1:
        raise ValueError("Invalid domain")
    if len(charts)!=seq.dimension+1:
        raise ValueError("Wrong number of rows")
    e=Emitter(bits)
    t=e.new("T",T,True)
    if bits is not None:
        e.nat("horizon_bound_slack", 2**bits-1-t)
    bases=[e.new("base",m.base,True) for m in seq.modes]
    for i,b in enumerate(bases):
        e.nat("base_order_slack",b-(bases[i-1] if i else 0)-1)
    current=[]
    for b,m in zip(bases,seq.modes):
        cs=[]
        for c in m.coefficients:
            p=e.new("coefficient_p",max(c,0),True)
            n=e.new("coefficient_n",max(-c,0),True)
            e.require(p*n)
            cs.append(Signed(p,n))
        current.append((b,cs))
    ladder=[current]
    for r in range(seq.dimension):
        kill=current[0][0]
        nxt=[]
        for i,(b,cs) in enumerate(current):
            size=len(cs)-(i==0)
            nc=[]
            for j in range(size):
                shifted=sum(comb(k,j)*cs[k].expr for k in range(j,len(cs)))
                nc.append(e.signed("ladder_coefficient",b*shifted-kill*cs[j].expr))
            if nc:
                nxt.append((b,nc))
        current=nxt
        ladder.append(current)
    rows=[]
    D=seq.dimension
    for r in range(D+1):
        capacity=max(1,2*(D-r)-1)
        if not 1<=len(charts[r])<=capacity:
            raise ValueError("Chart length outside capacity")
        row=[]
        for i in range(capacity):
            active=i<len(charts[r])
            block=charts[r][i] if active else None
            a=e.boolean("active",active)
            lo=e.new("lo",block.lo if active else 0)
            hi=e.new("hi",block.hi if active else 0)
            signs=tuple(e.new("claimed_sign",int(active and block.sign==s))
                        for s in (1,0,-1))
            e.require(sum(signs)-a)
            e.require((1-a)*lo)
            e.require((1-a)*hi)
            e.nat("length_slack",hi-lo)
            e.nat("endpoint_bound_slack",t-hi)
            row.append((a,lo,hi,signs))
        e.require(row[0][0]-1)
        e.require(row[0][1])
        for i,(a,lo,hi,sg) in enumerate(row):
            next_active=row[i+1][0] if i+1<len(row) else Poly.as_poly(0)
            e.require((a-next_active)*(hi-t))
            if i+1<len(row):
                an,ln,hn,sn=row[i+1]
                e.require(an*(1-a))
                e.require(an*(ln-hi-1))
                e.require(sum(x*y for x,y in zip(sg,sn)))
        rows.append(row)
    # The last row is the identically-zero sequence, anchored canonically.
    a,lo,hi,sg=rows[-1][0]
    for actual,target in zip(sg,(0,1,0)):
        e.require(actual-target)

    def evaluate(row_index,time):
        terms=[]
        for b,cs in ladder[row_index]:
            acc=cs[-1]
            for c in reversed(cs[:-1]):
                acc=e.signed("horner",acc.expr*time+c.expr)
            power=e.power(b,time)
            term=e.signed("mode_value",acc.expr*power)
            terms.append(term.expr)
        value=e.signed("sequence_value",sum(terms))
        return e.sign_bits(value.expr)

    for r in range(D):
        for au,lu,hu,su in rows[r]:
            for al,ll,hl,sl in rows[r+1]:
                _,left=e.minmax(lu,ll)
                expanded=e.nat("lower_vertex_end",hl+1)
                right,_=e.minmax(hu,expanded)
                right,_=e.minmax(right,t)
                nonempty=e.le(left,right)
                both=e.nat("both_active",au*al)
                check=e.nat("check_intersection",both*nonempty)
                for time in (left,right):
                    actual=evaluate(r,time)
                    for claim,truth in zip(su,actual):
                        e.require(check*(claim-truth))
    if require_nonnegative:
        for a,lo,hi,sg in rows[0]:
            e.require(sg[2])
    return e


def verify_export(path: str | Path) -> bool:
    """Re-evaluate the serialized residuals; no use of the emitter's evaluator."""
    d=json.loads(Path(path).read_text())
    v=d["values"]
    if any(not isinstance(x,int) or x<0 for x in v):
        return False
    for residual in d["residuals"]:
        total=0
        for coefficient,indices in residual:
            if len(indices)>2:
                return False
            term=coefficient
            for i in indices:
                term*=v[i]
            total+=term
        if total:
            return False
    return all(pow(v[b],v[t])==v[y] for b,t,y in d["power_atoms"])
