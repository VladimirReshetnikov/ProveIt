#!/usr/bin/env python3
"""Independent checks for the ten-positive saturated, centered equation.

Standard library only.  This imports no producer or inherited verifier.
Finite controls check transcription; review.md supplies the unbounded proof
audit.  Usage: python3 ten_saturation_review.py --equation PATH [--output PATH]
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import itertools
import json
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path
import random


def require(value, message):
    if not value:
        raise ValueError(message)


class Poly:
    """Small exact sparse integer polynomial ring, used only at six cuts."""
    def __init__(self, n, terms=None):
        self.n = n
        self.terms = {e: c for e, c in (terms or {}).items() if c}

    @classmethod
    def constant(cls, n, c):
        return cls(n, {(0,) * n: c})

    @classmethod
    def variable(cls, n, i):
        e = [0] * n
        e[i] = 1
        return cls(n, {tuple(e): 1})

    def coerce(self, other):
        return other if isinstance(other, Poly) else Poly.constant(self.n, other)

    def __add__(self, other):
        other = self.coerce(other)
        out = dict(self.terms)
        for e, c in other.terms.items():
            out[e] = out.get(e, 0) + c
        return Poly(self.n, out)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.n, {e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        out = {}
        for e, c in self.terms.items():
            for f, d in other.terms.items():
                ef = tuple(a + b for a, b in zip(e, f))
                out[ef] = out.get(ef, 0) + c * d
        return Poly(self.n, out)

    __rmul__ = __mul__

    def __pow__(self, n):
        require(n >= 0, "negative polynomial exponent")
        ans = Poly.constant(self.n, 1)
        x = self
        while n:
            if n & 1:
                ans = ans * x
            n >>= 1
            if n:
                x = x * x
        return ans

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    def weighted_degree(self, weights):
        return max((sum(ei * wi for ei, wi in zip(e, weights))
                    for e in self.terms), default=-1)

    def top(self, weights):
        d = self.weighted_degree(weights)
        return Poly(self.n, {e: c for e, c in self.terms.items()
                            if sum(ei * wi for ei, wi in zip(e, weights)) == d})


def evaluate(rows, env, modulus=None):
    v = dict(env)
    for name, op, a, b in rows:
        a = a if isinstance(a, int) else v[a]
        b = b if isinstance(b, int) else v[b]
        if op == "+":
            r = a + b
        elif op == "-":
            r = a - b
        elif op == "*":
            r = a * b
        else:
            raise ValueError("illegal arithmetic operation")
        v[name] = r if modulus is None else r % modulus
    return v


def exact_algebra(rows):
    # The saturated strong radicand, its coprimality identity and root bound.
    A, j, d = [Poly.variable(3, i) for i in range(3)]
    delta0 = A * A - 1
    f2 = 1 + delta0 * d * j * j
    prod = d * f2
    center = A * j * d
    gap = j * j * d * d - d
    require(center * center - prod == gap, "root-bound identity")
    require(f2 - delta0 * d * j * j == 1, "coprimality identity")
    # Elimination of equal roots: the cleared difference is 1 mod d.
    # The simple integer polynomial quotient is checked in its own ring.
    D, F, Qpart, V = [Poly.variable(4, i) for i in range(4)]
    equal_difference = (D * Qpart - 1) * D * F - (D * Qpart * V * V - 1)
    require(equal_difference == 1 + D * ((D * Qpart - 1) * F - Qpart * V * V),
            "equal-root exclusion identity")

    # Four literal conjugates, rather than a second copy of the emitter.
    z, rr, yy = [Poly.variable(3, i) for i in range(3)]
    conj = Poly.constant(3, 1)
    for sr, sy in itertools.product((-1, 1), repeat=2):
        conj *= z - sr * rr - sy * yy
    require(conj == (z*z - rr*rr - yy*yy)**2 - 4*rr*rr*yy*yy,
            "four-conjugate identity")

    # All tail gates are replayed exactly at independent polynomial cuts.
    M, V, P, L, Q, E = [Poly.variable(6, i) for i in range(6)]
    delta = Q - 1
    prod = P * P - L
    dnum = Q * V * V - 1
    z = M * (V + P) + E
    cuts = {"Mtot": M, "delta": delta, "Dprod": prod,
            "Dnum": dnum, "Znum": z}
    started = False
    tail = []
    for row in rows:
        if row[0] == "M2":
            started = True
        if started and row[0] != "Dprod":
            tail.append(row)
    require(started, "missing expected norm cut")
    value = evaluate(tail, cuts)["N"]
    independent_norm = (delta*z*z-M*M*(delta*prod+dnum))**2 - 4*delta*M**4*prod*dnum
    require(value == independent_norm, "full emitted tail versus norm identity")

    B = M*M*L + 2*M*P*E + E*E
    C = delta*B - M*M*(V*V-1)
    pieces = [4*delta*V*V*M*M*(delta*B-M*M*prod),
              4*delta*V*M*(M*P+E)*C, C*C, 4*delta*prod*M**4]
    require(value == sum(pieces), "centered degree identity")
    weights = [13, 42, 28, 46, 48, 19]
    bounds = [p.weighted_degree(weights) for p in pieces]
    require(bounds == [278, 264, 240, 156], "centered degree bounds")
    top = 4*Q*Q*V*V*M**4*L
    require(value.top(weights) == top, "unique degree-278 top form")

    # Substitute the true leading forms in a small free polynomial ring.
    q, i, w, y, k, f = [Poly.variable(6, a) for a in range(6)]
    aa = q**3*w*y
    dt = q**10*w*w*y**4*k*k
    ii = i*k*k*y*y
    qq = aa**4*dt*ii*ii
    vv = -(aa*aa*dt*ii*ii) * q**3*(q-f)
    mm = 4*q**11*w*y
    ll = ii*ii*dt*dt
    lead = 4*qq*qq*vv*vv*mm**4*ll
    expected = 2**10*q**146*i**10*w**28*y**60*k**32*(q-f)**2
    require(lead == expected, "actual leading-form substitution")
    require(sum((146,10,28,60,32,2)) == 278, "selected monomial degree")
    return {"exact_identities": 8, "norm_tail_gates": len(tail),
            "centered_term_degrees": bounds, "exact_degree": 278,
            "leading_form": "2^10 q0^146 i^10 w^28 Y^60 (eta+zeta)^32 (q0-F)^2",
            "selected_monomial": "J^146 i^10 w^28 Y^60 eta^32 F^2",
            "selected_coefficient": "2^10 beta^146 > 0"}


def census(packet):
    rows = packet["source"]
    known = set(packet["witnesses"]) | set(packet["fixed_numerals"])
    graph = {}
    counts = {"+": 0, "-": 0, "*": 0}
    for name, op, a, b in rows:
        require(name not in known, "duplicate name")
        require(op in counts, "nonpolynomial operation")
        require(all(isinstance(x, int) or x in known for x in (a,b)), "forward or missing input")
        graph[name] = [x for x in (a,b) if isinstance(x, str)]
        known.add(name)
        counts[op] += 1
    live = set()
    pending = [packet["output"]]
    while pending:
        x = pending.pop()
        if x not in live:
            live.add(x)
            pending.extend(graph.get(x, []))
    require(all(x in live for x in known), "dead gate or input")
    require(counts == {"+":22,"-":16,"*":55}, "unexpected binary census")
    require(len(packet["witnesses"]) == 10, "wrong witness count")
    require(packet["domain"] == "strictly positive integers", "wrong domain")
    return {"unknowns":10,"operations":sum(counts.values()),"breakdown":counts,"all_inputs_and_gates_live":True}


def independent_front(inputs, ports, p):
    J,F,al,w,Y,eta,zeta,i,T,n = [inputs[x] for x in ("J","F","alpha","w","Y","eta","zeta","i","T","n")]
    beta,K0,MC,MF = [ports[x] for x in ("beta","K0","MC","MF")]
    q=(beta*J+1)%p; mu=(q*q+1)%p; X=w*q%p; k=(eta+zeta)%p; c=(k*Y+eta)%p
    A=(mu*Y*(X+1)+1)%p; H=(4*A-5)%p; Dp=(A*A-1)%p
    v0=X*mu*mu*Y*Y%p; dt=(1+v0*(v0+1)*k*k)%p
    I=i*c*c%p; df=(1+Dp*dt*I*I)%p; Q=Dp*Dp*dt*I*I%p; de=(Q-1)%p
    R=(((q-1)*(q-F)+al)*(q*q-1)+(MC+q*MF)*J)%p
    b=(c*(T+al)-R)%p; V=(df*b-c)%p; dn=(Q*V*V-1)%p
    P=A*I*dt%p; W=(1+(q-1)*b)%p; Bt=((K0+w)*(q-F-al)-F)%p
    kp=(X*(3*c-2*X)+2)%p; e=(k-R-1)%p
    M=mu*mu*q**3*(q-1)*H%p
    Z=(mu*mu*q**3*(q-1)*(H*(n+V+P)+kp)
       +H*(mu*mu*((q-1)*Y-q**3*W*Bt)-q**3*(q-1)*e))%p
    return {"q":q,"mu":mu,"X":X,"k":k,"c":c,"A":A,"Hp":H,
            "Dp":Dp,"Dtau":dt,"I":I,"Df":df,"Q":Q,"delta":de,
            "R":R,"cTR":b,"V":V,"Dnum":dn,"Pcenter":P,"W":W,
            "Bt":Bt,"Kpos":kp,"e":e,"Mtot":M,"Znum":Z,"Dprod":dt*df%p}


def multiply_quadratic(a, b, r2, y2, p):
    # Basis 1,r,y,ry, with independent formal signs.
    out=[0]*4
    for u,x in enumerate(a):
        for v,y in enumerate(b):
            co=x*y
            if (u&1) and (v&1): co*=r2
            if (u&2) and (v&2): co*=y2
            out[u^v]=(out[u^v]+co)%p
    return out


def modular_controls(packet, directory):
    binding=packet["coefficient_binding"]
    ports={}; hashes={}
    for name, spec in binding["ports"].items():
        raw=gzip.decompress((directory/binding["path"]/spec["file"]).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==spec["raw_sha256"], "actual coefficient hash")
        ports[name]=int.from_bytes(raw,"little")
        hashes[name]=spec["raw_sha256"]
    require(ports["beta"] == 2**590069-1, "wrong whole beta binding")
    rng=random.Random(20261024)
    comparisons=0; outputs=0
    for p in (1000000007,1000000009,2305843009213693951):
        pp={k:v%p for k,v in ports.items()}
        for case in range(80):
            ins={k:rng.randrange(1,30) for k in packet["witnesses"]}
            if case<20:
                ins={k:rng.randrange(-5,6) for k in packet["witnesses"]}
            val=evaluate(packet["source"],{**ins,**pp},p)
            ref=independent_front(ins,pp,p)
            for k,x in ref.items():
                require(val[k]==x, "independent front mismatch: "+k)
                comparisons+=1
            de=ref["delta"]; M=ref["Mtot"]; Z=ref["Znum"]
            if de:
                yy=ref["Dnum"]*pow(de,p-2,p)%p
                prod=[1,0,0,0]
                for sr,sy in itertools.product((-1,1),repeat=2):
                    prod=multiply_quadratic(prod,[Z,-sr*M,-sy*M,0],ref["Dprod"],yy,p)
                require(prod[1:]==[0,0,0],"formal conjugates fail sign invariance")
                require(prod[0]*de*de%p==val["N"],"independent conjugate norm output")
            else:
                require(val["N"]==M**4*ref["Dnum"]**2%p,"denominator-zero polynomial identity")
            outputs+=1
    return {"actual_coefficient_raw_hashes":hashes,"front_register_diagnostics":comparisons,
            "four_conjugate_output_diagnostics":outputs,
            "scope":"Finite transcription controls, not proofs of native semantics or consistency."}


def pell_pair(a,n):
    x,y=1,0
    for _ in range(n):
        x,y=a*x+(a*a-1)*y, x+a*y
    return x,y


def toy_controls():
    inequalities=0
    for A in range(3,14):
        delta=A*A-1
        for tau in range(2,12):
            dt=tau*tau
            for I in range(1,8):
                f2=1+delta*dt*I*I
                P=A*I*dt; Q=delta*delta*dt*I*I
                require(P*P>dt*f2,"strict root center bound")
                require(Q>P,"Q dominates the center")
                require(gcd(dt,f2)==1,"saturated roots are coprime")
                inequalities+=1
    auxiliary=0
    for S in range(2,15):
        Q=S*S
        for R in (5,7,9):
            x,y=pell_pair(S,R)
            require(x%S==0,"odd auxiliary quotient")
            V=x//S
            require(Q*V*V-(Q-1)*y*y==1,"auxiliary norm")
            require(y-V>=8*Q-4,"auxiliary gap")
            require(V>Q*Q,"auxiliary quotient growth")
            auxiliary+=1
    rational_controls=0
    for Q in range(2,70):
        for V in range(-25,26):
            f=Fraction(Q*V*V-1,Q-1)
            if f<0: continue
            a,b=isqrt(f.numerator),isqrt(f.denominator)
            if a*a==f.numerator and b*b==f.denominator:
                require(b==1,"rational adjacent root is integral")
                rational_controls+=1
    # Exact finite matrix order modulo arbitrary targets. The theorem uses
    # finiteness and determinant 1, not an empirical period bound.
    periods=[]
    for A in (3,4,5,7):
        for modulus in (2,3,5,7,9,11,16,25,35):
            x,y=1,0
            for n in range(1,10001):
                x,y=(A*x+(A*A-1)*y)%modulus,(x+A*y)%modulus
                if x==1 and y==0:
                    periods.append([A,modulus,n]); break
            else: raise ValueError("toy period cap exceeded")
    return {"root_center_and_coprimality_cases":inequalities,
            "auxiliary_gap_cases":auxiliary,"rational_adjacent_roots":rational_controls,
            "matrix_period_controls":periods,
            "scope":"Diagnostics for general identities; the finite-group argument proves arbitrary-modulus availability."}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--equation",type=Path,required=True)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    raw=args.equation.read_bytes(); packet=json.loads(raw)
    result={"status":"pass","equation_sha256":hashlib.sha256(raw).hexdigest(),
            "census":census(packet),"exact_algebra":exact_algebra(packet["source"]),
            "transcription":modular_controls(packet,args.equation.parent),
            "toy_controls":toy_controls(),
            "limits":"No native-calibration replay, proof-assistant theorem, internal-ZFC derivation, or minimality claim."}
    encoded=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.output: args.output.write_text(encoded)
    print(encoded)


if __name__=="__main__":
    main()
