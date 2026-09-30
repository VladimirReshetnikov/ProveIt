"""Exact witness-faithful Diophantine compilers (Python 3.10+, standard library).

A system stores integer polynomial residuals. Its one-equation interpretation is
sum(residual**2) == 0 with ALL variables ranging over NONNEGATIVE INTEGERS.
No search procedure for general Diophantine equations is claimed.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from math import isqrt
from typing import Iterable, Mapping, Sequence
import json

@dataclass
class Poly:
    terms: dict[tuple[str, ...], int]

    def __post_init__(self) -> None:
        self.terms = {tuple(sorted(m)): int(c) for m, c in self.terms.items() if c}

    @staticmethod
    def cast(value: int | Poly) -> Poly:
        return value if isinstance(value, Poly) else Poly({(): int(value)})

    def __add__(self, other: int | Poly) -> Poly:
        out = dict(self.terms)
        for monomial, coefficient in Poly.cast(other).terms.items():
            out[monomial] = out.get(monomial, 0) + coefficient
        return Poly(out)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: int | Poly) -> Poly:
        return self + (-Poly.cast(other))

    def __rsub__(self, other: int | Poly) -> Poly:
        return Poly.cast(other) + (-self)

    def __mul__(self, other: int | Poly) -> Poly:
        out: dict[tuple[str, ...], int] = {}
        for a, c in self.terms.items():
            for b, d in Poly.cast(other).terms.items():
                monomial = tuple(sorted(a + b))
                out[monomial] = out.get(monomial, 0) + c * d
        return Poly(out)

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: Mapping[str, int]) -> int:
        result = 0
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for name in monomial:
                term *= values[name]
            result += term
        return result

    def as_json(self) -> list[dict]:
        return [{"coefficient": c, "monomial": list(m)}
                for m, c in sorted(self.terms.items())]

@dataclass
class System:
    variables: list[str] = field(default_factory=list)
    residuals: list[tuple[str, Poly]] = field(default_factory=list)
    witness: dict[str, int] = field(default_factory=dict)

    def var(self, name: str, value: int | None = None) -> Poly:
        if name in self.variables:
            raise ValueError(f"Duplicate variable: {name}")
        self.variables.append(name)
        if value is not None:
            if not isinstance(value, int) or value < 0:
                raise ValueError(f"Not a natural value: {name}={value}")
            self.witness[name] = value
        return Poly({(name,): 1})

    def eq(self, label: str, residual: int | Poly) -> None:
        self.residuals.append((label, Poly.cast(residual)))

    def values(self, assignment: Mapping[str, int] | None = None) -> list[int]:
        v = self.witness if assignment is None else assignment
        if set(v) != set(self.variables):
            raise ValueError("Assignment must specify exactly the system variables")
        if any(not isinstance(x, int) or x < 0 for x in v.values()):
            raise ValueError("The domain is the nonnegative integers")
        return [p.evaluate(v) for _, p in self.residuals]

    def energy(self, assignment: Mapping[str, int] | None = None) -> int:
        return sum(x*x for x in self.values(assignment))

    def dump(self, path: str) -> None:
        data = {"domain": "nonnegative integers", "combination": "sum of squared residuals",
                "variables": self.variables,
                "residuals": [{"label": k, "polynomial": p.as_json()}
                              for k, p in self.residuals],
                "witness": self.witness,
                "residual_degree_bound": max((p.degree for _, p in self.residuals), default=0)}
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(data, handle, indent=2)
            handle.write("\n")


def monitor(word: Sequence[int], alphabet_size: int,
            independent: set[tuple[int, int]]) -> tuple[bool, list[list[int]]]:
    """Recognize the lexicographically least word in its commutation class."""
    flags = [0] * alphabet_size
    rows = [flags.copy()]
    good = True
    for letter in word:
        if not 0 <= letter < alphabet_size:
            raise ValueError("Letter outside alphabet")
        good = good and flags[letter] == 0
        flags = [int((letter, a) in independent) *
                 (1 if letter > a else flags[a]) for a in range(alphabet_size)]
        rows.append(flags.copy())
    return good, rows

@dataclass(frozen=True)
class PetriNet:
    # Each row is the vector for one labeled transition.
    pre: tuple[tuple[int, ...], ...]
    post: tuple[tuple[int, ...], ...]

    def __post_init__(self) -> None:
        if not self.pre or len(self.pre) != len(self.post):
            raise ValueError("Provide equally many nonempty pre/post transition rows")
        p = len(self.pre[0])
        if not p or any(len(row) != p for row in self.pre + self.post):
            raise ValueError("Inconsistent number of places")
        if any(not isinstance(x, int) or x < 0 for row in self.pre + self.post for x in row):
            raise ValueError("Arc weights must be natural integers")

    @property
    def p(self) -> int:
        return len(self.pre[0])

    @property
    def r(self) -> int:
        return len(self.pre)

    def independence(self) -> set[tuple[int, int]]:
        support = [{p for p in range(self.p) if self.pre[a][p] or self.post[a][p]}
                   for a in range(self.r)]
        return {(a, b) for a in range(self.r) for b in range(self.r)
                if a != b and support[a].isdisjoint(support[b])}

    def run(self, start: Sequence[int], word: Sequence[int]) -> list[tuple[int, ...]] | None:
        if len(start) != self.p or any(x < 0 for x in start):
            raise ValueError("Invalid marking")
        rows = [tuple(start)]
        for a in word:
            if not 0 <= a < self.r:
                raise ValueError("Invalid transition")
            if any(rows[-1][p] < self.pre[a][p] for p in range(self.p)):
                return None
            rows.append(tuple(rows[-1][p] - self.pre[a][p] + self.post[a][p]
                              for p in range(self.p)))
        return rows


def compile_petri(net: PetriNet, start: Sequence[int], finish: Sequence[int], horizon: int,
                  word: Sequence[int] | None = None,
                  independent: set[tuple[int, int]] | None = None) -> System:
    if horizon < 0 or len(start) != net.p or len(finish) != net.p:
        raise ValueError("Invalid horizon or endpoint dimensions")
    if any(x < 0 for x in tuple(start)+tuple(finish)):
        raise ValueError("Markings must be natural")
    indep = net.independence() if independent is None else independent
    if not indep <= net.independence() or any((b,a) not in indep for a,b in indep):
        raise ValueError("Independence must be symmetric and have disjoint supports")
    rows = flags = None
    if word is not None:
        if len(word) != horizon:
            raise ValueError("Word has wrong length")
        rows = net.run(start, word)
        if rows is None:
            raise ValueError("Word is not enabled")
        _, flags = monitor(word, net.r, indep)
    s = System()
    m = [[s.var(f"m_{t}_{p}", None if rows is None else rows[t][p])
          for p in range(net.p)] for t in range(horizon+1)]
    x = [[s.var(f"x_{t}_{a}", None if word is None else int(word[t] == a))
          for a in range(net.r)] for t in range(horizon)]
    e = [[s.var(f"e_{t}_{p}", None if rows is None else rows[t][p]-net.pre[word[t]][p])
          for p in range(net.p)] for t in range(horizon)]
    f = [[s.var(f"f_{t}_{a}", None if flags is None else flags[t][a])
          for a in range(net.r)] for t in range(horizon+1)]
    for p in range(net.p):
        s.eq(f"initial_{p}", m[0][p]-start[p])
        s.eq(f"final_{p}", m[horizon][p]-finish[p])
    for a in range(net.r):
        s.eq(f"monitor_initial_{a}", f[0][a])
    for t in range(horizon):
        for a in range(net.r):
            s.eq(f"selector_boolean_{t}_{a}", x[t][a]*(x[t][a]-1))
        s.eq(f"one_transition_{t}", sum(x[t])-1)
        for p in range(net.p):
            pre = sum(net.pre[a][p]*x[t][a] for a in range(net.r))
            post = sum(net.post[a][p]*x[t][a] for a in range(net.r))
            s.eq(f"enabled_{t}_{p}", m[t][p]-pre-e[t][p])
            s.eq(f"update_{t}_{p}", m[t+1][p]+pre-m[t][p]-post)
        for a in range(net.r):
            lower = sum(x[t][c] for c in range(a) if (c,a) in indep)
            upper = sum(x[t][c] for c in range(a+1,net.r) if (c,a) in indep)
            s.eq(f"monitor_update_{t}_{a}", f[t+1][a]-f[t][a]*lower-upper)
        s.eq(f"normal_form_{t}", sum(x[t][a]*f[t][a] for a in range(net.r)))
    return s


def normalize_fractions(program: Sequence[tuple[int,int]]) -> list[tuple[int,int]]:
    out = []
    for a,b in program:
        if not isinstance(a,int) or not isinstance(b,int) or a <= 0 or b <= 0:
            raise ValueError("FRACTRAN fractions must be positive integers")
        q = Fraction(a,b)
        out.append((q.numerator,q.denominator))
    if not out:
        raise ValueError("This implementation expects a nonempty program")
    return out


def fractran_run(program: Sequence[tuple[int,int]], start: int, horizon: int) -> list[int] | None:
    prog = normalize_fractions(program)
    if start <= 0 or horizon < 0:
        raise ValueError("Positive input and natural horizon required")
    rows = [start]
    for _ in range(horizon):
        for a,b in prog:
            if rows[-1] % b == 0:
                rows.append(a*(rows[-1]//b))
                break
        else:
            return None
    return rows


def compile_fractran(program: Sequence[tuple[int,int]], start: int, finish: int,
                     horizon: int, *, witness: bool = True, terminal: bool = False) -> System:
    prog = normalize_fractions(program)
    if start <= 0 or finish <= 0 or horizon < 0:
        raise ValueError("Positive endpoints and natural horizon required")
    rows = fractran_run(prog,start,horizon) if witness else None
    if witness and rows is None:
        raise ValueError("Program halts before the requested horizon")
    s = System()
    n = [s.var(f"n_{t}", None if rows is None else rows[t]) for t in range(horizon+1)]
    s.eq("initial",n[0]-start)
    s.eq("final",n[-1]-finish)
    for t in range(horizon):
        hv = 1
        h = s.var(f"h_{t}_0", None if rows is None else 1)
        s.eq(f"prefix_initial_{t}",h-1)
        selected: list[Poly] = []
        products: list[Poly] = []
        for j,(a,b) in enumerate(prog,1):
            if rows is None:
                qv=rv=sv=uv=zv=xv=hnextv=None
            else:
                qv,rv = divmod(rows[t],b)
                sv=b-1-rv
                zv=int(rv==0)
                uv=0 if zv else rv-1
                xv=hv*zv
                hnextv=hv*(1-zv)
            q=s.var(f"q_{t}_{j}",qv)
            rem=s.var(f"rem_{t}_{j}",rv)
            gap=s.var(f"gap_{t}_{j}",sv)
            u=s.var(f"u_{t}_{j}",uv)
            z=s.var(f"z_{t}_{j}",zv)
            hnext=s.var(f"h_{t}_{j}",hnextv)
            x=s.var(f"x_{t}_{j}",xv)
            s.eq(f"divide_{t}_{j}",n[t]-b*q-rem)
            s.eq(f"remainder_bound_{t}_{j}",rem+gap-(b-1))
            s.eq(f"zero_bit_{t}_{j}",z*(z-1))
            s.eq(f"zero_test_{t}_{j}",z*rem)
            s.eq(f"positive_test_{t}_{j}",rem-(1-z)*(u+1))
            s.eq(f"inactive_zero_{t}_{j}",z*u)
            s.eq(f"prefix_{t}_{j}",hnext-h*(1-z))
            s.eq(f"first_applicable_{t}_{j}",x-h*z)
            h=hnext
            if hnextv is not None:
                hv=hnextv
            selected.append(x)
            products.append(a*q*x)
        s.eq(f"nonterminal_{t}",sum(selected)-1)
        s.eq(f"output_{t}",n[t+1]-sum(products))
    if terminal:
        for j,(_,b) in enumerate(prog,1):
            if rows is None:
                qv=uv=vv=None
            else:
                qv,rem=divmod(rows[-1],b)
                if not rem:
                    raise ValueError("Endpoint is not terminal")
                uv=rem-1
                vv=b-1-rem
            q=s.var(f"terminal_q_{j}",qv)
            u=s.var(f"terminal_u_{j}",uv)
            v=s.var(f"terminal_v_{j}",vv)
            s.eq(f"terminal_divide_{j}",n[-1]-b*q-u-1)
            s.eq(f"terminal_positive_remainder_{j}",u+v-(b-2))
    return s


# Every natural is the code of a finite SKI tree: S=0,K=1,I=2.
def app(left: int, right: int) -> int:
    if left < 0 or right < 0:
        raise ValueError("Natural term codes required")
    k=left+right
    return 3+k*(k+1)//2+right


def unapp(code: int) -> tuple[int,int]:
    if code < 3:
        raise ValueError("A leaf is not an application")
    z=code-3
    k=(isqrt(8*z+1)-1)//2
    right=z-k*(k+1)//2
    return k-right,right


def ski_step(code: int, rule: str, path: str) -> int:
    if any(d not in 'LR' for d in path) or rule not in ('S','K','I'):
        raise ValueError("Use rules S,K,I and paths over L,R")
    if path:
        left,right=unapp(code)
        return app(ski_step(left,rule,path[1:]),right) if path[0]=='L' \
            else app(left,ski_step(right,rule,path[1:]))
    if rule=='I':
        head,x=unapp(code)
        if head!=2:
            raise ValueError("Not an I redex")
        return x
    if rule=='K':
        inner,y=unapp(code)
        head,x=unapp(inner)
        if head!=1:
            raise ValueError("Not a K redex")
        return x
    inner,z=unapp(code)
    innermost,y=unapp(inner)
    head,x=unapp(innermost)
    if head!=0:
        raise ValueError("Not an S redex")
    return app(app(x,z),app(y,z))


def compile_ski(start: int, finish: int, schedule: Sequence[tuple[str,str]],
                *, witness: bool = True) -> System:
    if start < 0 or finish < 0:
        raise ValueError("Natural endpoints required")
    if any(rule not in ('S','K','I') or any(d not in 'LR' for d in path)
           for rule,path in schedule):
        raise ValueError("Invalid schedule")
    rows=None
    if witness:
        rows=[start]
        for rule,path in schedule:
            rows.append(ski_step(rows[-1],rule,path))
    s=System()
    configs=[s.var(f"c_{t}",None if rows is None else rows[t])
             for t in range(len(schedule)+1)]
    s.eq('initial',configs[0]-start)
    s.eq('final',configs[-1]-finish)
    def app_eq(label: str,node: Poly,left: int|Poly,right: int|Poly) -> None:
        z=Poly.cast(left)+right
        s.eq(label,2*node-6-z*(z+1)-2*Poly.cast(right))
    for t,(rule,path) in enumerate(schedule):
        src=configs[t]
        dest=configs[t+1]
        srcv=None if rows is None else rows[t]
        destv=None if rows is None else rows[t+1]
        for depth,direction in enumerate(path):
            if srcv is None:
                childv=siblingv=newchildv=None
            else:
                pair=unapp(srcv)
                newpair=unapp(destv)
                chosen=0 if direction=='L' else 1
                childv,siblingv=pair[chosen],pair[1-chosen]
                newchildv=newpair[chosen]
                if newpair[1-chosen]!=siblingv:
                    raise AssertionError("Context sibling changed")
            child=s.var(f"oldchild_{t}_{depth}",childv)
            sibling=s.var(f"sibling_{t}_{depth}",siblingv)
            newchild=s.var(f"newchild_{t}_{depth}",newchildv)
            if direction=='L':
                app_eq(f"context_old_{t}_{depth}",src,child,sibling)
                app_eq(f"context_new_{t}_{depth}",dest,newchild,sibling)
            else:
                app_eq(f"context_old_{t}_{depth}",src,sibling,child)
                app_eq(f"context_new_{t}_{depth}",dest,sibling,newchild)
            src,dest=child,newchild
            srcv,destv=childv,newchildv
        def new(name: str,value: int | None) -> Poly:
            return s.var(f"{name}_{t}",value)
        if rule=='I':
            xv=None if srcv is None else unapp(srcv)[1]
            x=new('arg',xv)
            app_eq(f"redex_I_{t}",src,2,x)
            s.eq(f"contract_I_{t}",dest-x)
        elif rule=='K':
            if srcv is None:
                hv=xv=yv=None
            else:
                hv,yv=unapp(srcv)
                _,xv=unapp(hv)
            h=new('head',hv);x=new('x',xv);y=new('y',yv)
            app_eq(f"redex_K_outer_{t}",src,h,y)
            app_eq(f"redex_K_inner_{t}",h,1,x)
            s.eq(f"contract_K_{t}",dest-x)
        else:
            if srcv is None:
                hv=gv=xv=yv=zv=pv=qv=None
            else:
                hv,zv=unapp(srcv);gv,yv=unapp(hv);_,xv=unapp(gv)
                pv=app(xv,zv);qv=app(yv,zv)
            h=new('head',hv);g=new('inner',gv)
            x=new('x',xv);y=new('y',yv);z=new('z',zv)
            p=new('left_result',pv);q=new('right_result',qv)
            app_eq(f"redex_S_outer_{t}",src,h,z)
            app_eq(f"redex_S_middle_{t}",h,g,y)
            app_eq(f"redex_S_inner_{t}",g,0,x)
            app_eq(f"contract_S_left_{t}",p,x,z)
            app_eq(f"contract_S_right_{t}",q,y,z)
            app_eq(f"contract_S_root_{t}",dest,p,q)
    return s


def mutation_audit(system: System) -> int:
    """Reject every one-coordinate +/-1 perturbation of a valid witness."""
    if system.energy()!=0:
        raise ValueError("Audit needs a valid witness")
    count=0
    for name in system.variables:
        for delta in (-1,1):
            values=dict(system.witness)
            values[name]+=delta
            if values[name]>=0:
                if system.energy(values)==0:
                    raise AssertionError(f"Undetected mutation {name}, {delta}")
                count+=1
    return count
