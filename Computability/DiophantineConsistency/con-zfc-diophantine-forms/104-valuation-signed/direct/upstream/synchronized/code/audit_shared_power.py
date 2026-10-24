#!/usr/bin/env python3
"""Independent symbolic and finite audit of shared positive-power graphs.

Run with the pinned upstream direct directory and this directory on PYTHONPATH.
No test assumes or attempts to decide the consistency of ZFC.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from math import gcd, prod
from pathlib import Path

from shared_power import SharedPowerBuilder
from build_equation import const


def require(ok, message):
    if not ok:
        raise ValueError(message)


class P:
    def __init__(self, terms=None):
        self.t = {m: c for m, c in (terms or {}).items() if c}

    @classmethod
    def var(cls, name):
        return cls({(name,): 1})

    @classmethod
    def coerce(cls, value):
        return value if isinstance(value, cls) else cls({(): value})

    def __add__(self, other):
        out = defaultdict(int, self.t)
        for m, c in self.coerce(other).t.items():
            out[m] += c
        return P(out)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.t.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        out = defaultdict(int)
        for ma, ca in self.t.items():
            for mb, cb in self.coerce(other).t.items():
                out[tuple(sorted(ma + mb))] += ca * cb
        return P(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        out = P.coerce(1)
        for _ in range(exponent):
            out = out * self
        return out

    def key(self):
        return tuple(sorted(self.t.items()))


def symbolic_rows(builder):
    values, constraints = {}, []
    for i, variable in enumerate(builder.variables):
        if i not in builder.gates:
            values[i] = P.var(variable["name"])
            continue
        row = builder.rows[builder.gates[i]]
        expression, coefficient = P(), 0
        for c, mon in row["terms"]:
            if mon == [i]:
                coefficient += c
            else:
                require(i not in mon and all(j < i for j in mon), "nontopological gate")
                term = P.coerce(c)
                for j in mon:
                    term *= values[j]
                expression += term
        require(coefficient == 1, "nonmonic gate")
        values[i] = -expression
    for row in builder.rows:
        if row["gate"] is not None:
            continue
        expression = P()
        for c, mon in row["terms"]:
            term = P.coerce(c)
            for j in mon:
                term *= values[j]
            expression += term
        constraints.append((row["label"], expression.key()))
    return values, Counter(constraints)


def exact_structure_audit():
    b = SharedPowerBuilder()
    n0, n1, k0, k1 = [b.new(s) for s in ("n0", "n1", "k0", "k1")]
    calls = [(n0, k0), (n1, k0), (n0, k1)]
    outputs = [b.power(n, k) for n, k in calls]
    require(b.power(n0, k0) == outputs[0], "power cache changed output")
    b.finalize_power_frame()
    values, actual = symbolic_rows(b)
    names = {v["name"]: values[i] for i, v in enumerate(b.variables)}
    at = lambda atom: P.coerce(atom[1]) if atom[0] == "c" else values[atom[1]]
    W, A, Z = names["shared.W"], names["shared.A"], names["shared.Zminus1"] + 1
    expected = [("shared.last_norm", (A*A-1-W**3*(W+2)*Z*Z).key())]
    all_atoms = {a for (n, k), m in zip(calls, outputs) for a in (n, k, m)}
    expected.append(("shared.frame_definition", (W-2-sum((at(a) for a in all_atoms), P())).key()))
    for j, k in enumerate((k0, k1)):
        prefix = "index" + str(j) + "."
        X,Y,U,V,S,R = [names[prefix+s] for s in ("X","Y","U","V","S","R")]
        B = 1+4*Y*(names[prefix+"q4minus1"]+1)
        norm = lambda a,x,y: x*x-1-(a*a-1)*y*y
        polynomials = {
            "index_at_most_Y": Y-at(k)-names[prefix+"YminusK"],
            "norm1": norm(A,X,Y),
            "norm2": norm(A,U,V),
            "norm3": norm(B,S,R),
            "V_positive_multiple": V-Y*Y*(names[prefix+"Vquotient_minus1"]+1),
            "B_mod_U": B-A-U*names[prefix+"Bquotient"],
            "S_mod_U": S-X-U*names[prefix+"Squotient"],
            "R_mod_4Y": R-at(k)-4*Y*names[prefix+"Rquotient"],
        }
        expected.extend((prefix+s, p.key()) for s,p in polynomials.items())
    for j,n in enumerate((n0,n1)):
        T = names["base"+str(j)+".T"]
        expected.append(("base"+str(j)+".T_definition", (2*A*at(n)-T-at(n)**2-1).key()))
    for j,((n,k),m) in enumerate(zip(calls,outputs)):
        index = 0 if k==k0 else 1
        base = 0 if n==n0 else 1
        X,Y = [names["index"+str(index)+"."+s] for s in ("X","Y")]
        T = names["base"+str(base)+".T"]
        p = X+Y*at(n)-A*Y-at(m)-T*names["pow"+str(j)+".quotient"]
        expected.append(("pow"+str(j)+".power_congruence",p.key()))
    require(actual == Counter(expected), "shared graph differs from mathematical constraints")
    require(len(b.shared_indices)==2 and len(b.shared_bases)==2, "cache census")
    require(b.shared_offset is None, "internal positive quotients used signed offset")
    # Identity making the quotient sign nonnegative.
    a,n,x,y = [P.var(s) for s in ("a","n","x","y")]
    T = 2*a*n-n*n-1
    H = x-(a-n)*y
    nextH = a*x+(a*a-1)*y-(a-n)*(x+a*y)
    require((nextH-n*H-T*y).t == {}, "Pell congruence recurrence identity")
    return {"semantic_power_calls":3,"distinct_exponent_certificates":2,
            "distinct_base_certificates":2,"exact_scalar_constraints":len(expected),
            "eliminated_definitional_gates":len(b.gates),
            "recurrence_identity":"H_(k+1)=n H_k+T Y_k"}


def pell(a,k):
    d=a*a-1
    x,y,u,v=1,0,a,1
    while k:
        if k&1:
            x,y=x*u+d*y*v,x*v+y*u
        u,v=u*u+d*v*v,2*u*v
        k//=2
    return x,y


def index_values(A,k):
    X,Y=pell(A,k)
    U,V=pell(A,2*k*Y)
    require(V>0 and V%(Y*Y)==0, "finite index divisibility")
    require(gcd(U,4*Y)==1, "finite index CRT coprimality")
    B=A+U*(((1-A)*pow(U,-1,4*Y))%(4*Y))
    if B<max(A,2):
        B += 4*Y*U
    S,R=pell(B,k)
    require(B>=A and S>=X and R>=k, "oriented finite quotients")
    require((B-A)%U==0 and (S-X)%U==0 and (R-k)%(4*Y)==0,
            "index finite congruences")
    return dict(X=X,Y=Y,U=U,V=V,S=S,R=R,B=B,
                YminusK=Y-k,q4minus1=(B-1)//(4*Y)-1,
                Vquotient_minus1=V//(Y*Y)-1,
                Bquotient=(B-A)//U,Squotient=(S-X)//U,Rquotient=(R-k)//(4*Y))


def evaluate(builder, assignment):
    values=[]
    for i,var in enumerate(builder.variables):
        if i in builder.gates:
            row=builder.rows[builder.gates[i]]
            c0,rest=0,0
            for c,mon in row["terms"]:
                if mon==[i]:
                    c0+=c
                else:
                    require(i not in mon and all(j<i for j in mon), "finite gate topology")
                    rest+=c*prod(values[j] for j in mon)
            require(c0==1,"finite nonmonic gate")
            value=-rest
        else:
            require(var["name"] in assignment,"missing finite witness: "+var["name"])
            value=assignment[var["name"]]
        require(value>=0,"negative finite witness")
        values.append(value)
    rows=[sum(c*prod(values[j] for j in mon) for c,mon in r["terms"]) for r in builder.rows]
    return values,rows


def finite_audit():
    fixture_count=mutations=0
    for bases in ((1,), (1,2), (1,2,3)):
        b=SharedPowerBuilder()
        for n in bases:
            b.power(const(n),const(1))
        b.finalize_power_frame()
        # Distinct scalar atoms remain separate even when their values agree.
        W=2+sum(set(bases)|{1})+sum(bases)
        A,Yframe=pell(W+1,W)
        require(Yframe%W==0 and Yframe>0,"frame divisibility")
        assignment={"shared.W":W,"shared.A":A,"shared.Zminus1":Yframe//W-1}
        index=index_values(A,1)
        for name,val in index.items():
            if name!="B":
                assignment["index0."+name]=val
        for j,n in enumerate(bases):
            T=2*A*n-n*n-1
            h=(index["X"]-(A-n)*index["Y"]-n)//T
            assignment.update({"base"+str(j)+".T":T,"pow"+str(j)+".output":n,
                               "pow"+str(j)+".quotient":h})
        values,rows=evaluate(b,assignment)
        require(not any(rows),"complete shared finite fixture")
        for j,n in enumerate(bases):
            changed=dict(assignment)
            changed["pow"+str(j)+".output"]=n+1
            require(any(evaluate(b,changed)[1]),"changed output escaped complete graph")
            mutations+=1
        fixture_count+=1
    # Nontrivial exponent witnesses tested separately at manageable Pell bases;
    # the exact structural audit covers their connection to the common frame.
    index_cases=0
    for A,k in ((2,1),(2,2),(3,2),(17,2)):
        z=index_values(A,k)
        for a,x,y in ((A,z["X"],z["Y"]),(A,z["U"],z["V"]),(z["B"],z["S"],z["R"])):
            require(x*x-(a*a-1)*y*y==1,"finite index norm")
        index_cases+=1
    congruence_cases=0
    for A in range(2,12):
        for n in range(1,A+1):
            T=2*A*n-n*n-1
            for k in range(1,9):
                X,Y=pell(A,k)
                numerator=X-(A-n)*Y-n**k
                require(numerator>=0 and numerator%T==0,"one-sided Pell power identity")
                congruence_cases+=1
    # Opposite quotient signs and modulus zero exercise the remaining offset.
    b=SharedPowerBuilder()
    for L,R,M in ((1,9,2),(9,1,2),(7,7,0)):
        b.congruent(const(L),const(R),const(M),"outer"+str(len(b.rows)))
    free={v["name"] for i,v in enumerate(b.variables) if i not in b.gates}
    offset={"shared.congruence_offset":4}
    qnames=[v["name"] for i,v in enumerate(b.variables) if i not in b.gates and v["name"]!="shared.congruence_offset"]
    offset.update(zip(qnames,(8,0,4)))
    require(set(offset)==free,"offset witness inventory")
    require(not any(evaluate(b,offset)[1]),"general congruence common offset")
    return {"complete_shared_graph_fixtures":fixture_count,
            "changed_outputs_rejected":mutations,"nontrivial_index_fixtures":index_cases,
            "one_sided_power_congruence_cases":congruence_cases,
            "signed_and_zero_modulus_offset_cases":3}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    result={"status":"PASS","exact_structure":exact_structure_audit(),
            "finite_controls":finite_audit(),"optimized_python":not __debug__,
            "scope":"Exact finite graph identities and finite controls; universal correctness is the ordinary proof, not these controls.",
            "sha256":{p.name:sha256(p.read_bytes()).hexdigest() for p in
                      (Path(__file__),Path(__file__).with_name("shared_power.py"))}}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=="__main__":
    main()
