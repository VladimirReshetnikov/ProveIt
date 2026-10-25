#!/usr/bin/env python3
"""Independent exact cut, leading-form, liveness, and fixed-numeral checks."""
from __future__ import annotations
import argparse
import ast
from collections import Counter
from copy import deepcopy
from dataclasses import dataclass
import gzip
import hashlib
import json
from pathlib import Path

from rebuild_coefficients import check_or_write

ROOT = Path(__file__).resolve().parent
INPUTS = ["J","F","alpha","i","T","w","s","n","eta","zeta"]
PORTS = ["beta","K0","MC","MF"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Ring:
    def __init__(self, names):
        self.names = list(names)
        self.index = {x:i for i,x in enumerate(names)}
        self.zero = (0,)*len(names)

    def constant(self, value):
        return Poly(self, {} if value == 0 else {self.zero:value})

    def variable(self, name):
        key=list(self.zero);key[self.index[name]]=1
        return Poly(self,{tuple(key):1})


class Poly:
    def __init__(self, ring, terms):
        self.ring=ring
        self.terms={m:c for m,c in terms.items() if c}

    def coerce(self, other):
        return self.ring.constant(other) if isinstance(other,int) else other

    def __add__(self, other):
        other=self.coerce(other);out=self.terms.copy()
        for mon,c in other.terms.items(): out[mon]=out.get(mon,0)+c
        return Poly(self.ring,out)
    __radd__=__add__

    def __neg__(self):
        return Poly(self.ring,{m:-c for m,c in self.terms.items()})

    def __sub__(self, other): return self + (-self.coerce(other))
    def __rsub__(self, other): return self.coerce(other) + (-self)

    def __mul__(self, other):
        other=self.coerce(other);out={}
        for a,ac in self.terms.items():
            for b,bc in other.terms.items():
                mon=tuple(x+y for x,y in zip(a,b))
                out[mon]=out.get(mon,0)+ac*bc
        return Poly(self.ring,out)
    __rmul__=__mul__

    def __pow__(self, exponent):
        require(isinstance(exponent,int) and exponent>=0,"Bad polynomial exponent")
        out=self.ring.constant(1);base=self
        while exponent:
            if exponent & 1: out=out*base
            exponent//=2
            if exponent: base=base*base
        return out

    def __eq__(self, other):
        return self.terms==self.coerce(other).terms


def expression(text, ring):
    def visit(node):
        if isinstance(node,ast.Name):return ring.variable(node.id)
        if isinstance(node,ast.Constant) and isinstance(node.value,int):return ring.constant(node.value)
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return -visit(node.operand)
        if isinstance(node,ast.BinOp):
            a=visit(node.left)
            if isinstance(node.op,ast.Pow):
                require(isinstance(node.right,ast.Constant),"Only constant powers are allowed")
                return a**node.right.value
            b=visit(node.right)
            if isinstance(node.op,ast.Add):return a+b
            if isinstance(node.op,ast.Sub):return a-b
            if isinstance(node.op,ast.Mult):return a*b
        raise ValueError("Unsupported symbolic expression")
    return visit(ast.parse(text,mode="eval").body)


def checks_for(weight):
    zweight="V**2" if weight=="V2" else "cTR*V"
    return [
      ("q",["beta","J"],"beta*J+1"),
      ("Y",["q","s"],"q**3*s"),
      ("C",["q","F","alpha"],"q-F-alpha"),
      ("X",["w","q"],"w*q"),
      ("k",["eta","zeta"],"eta+zeta"),
      ("c",["k","Y","eta"],"k*Y+eta"),
      ("Am1",["Y","X"],"Y*(X+1)"),
      ("Hp",["Am1"],"4*Am1-1"),
      ("Delta",["Am1"],"Am1*(Am1+2)"),
      ("Y2",["Y"],"Y**2"),
      ("V0",["X","Y2"],"X*Y2"),
      ("Dtau",["V0","k"],"1+V0*(V0+1)*k**2"),
      ("R",["bJ","q","F","alpha","MC","MF","J"],"(bJ*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J"),
      ("e",["k","R"],"k-R-1"),
      ("Bt",["K0","w","C","F"],"(K0+w)*C-F"),
      ("U",["i","c"],"i*c**2"),
      ("DpI2",["Delta","U","Dtau"],"Delta*U**2*Dtau"),
      ("Df",["DpI2"],"1+DpI2"),
      ("Fsqr",["DpI2"],"1+4*DpI2*(1+DpI2)"),
      ("Q",["Delta","DpI2"],"4*Delta*DpI2*(1+DpI2)"),
      ("cTR",["c","T","alpha","R"],"c*(T+alpha)-R"),
      ("V",["Fsqr","cTR","c"],"Fsqr*cTR-c"),
      ("Kpos",["X","c"],"X*(3*c-2*X)+2"),
      ("Mtot",["bJ","Y2","Hp"],"bJ*Y2*Hp"),
      ("Znum",["bJ","Y2","Hp","n","Bt","Kpos","e","V","cTR"],
       "bJ*Y2*(Hp*(n-("+zweight+")*Bt)+Kpos)-Hp*(Y2*Bt+bJ*e)"),
      ("Dg",["Dtau","Df"],"Dtau*Df"),
      ("RG",["Mtot","Dg"],"Mtot**2*Dg"),
      ("N",["Q","Znum","Mtot","Dg","V"],"Q*(Znum**2-Mtot**2*Dg*V**2)+(Mtot**2*Dg-Znum**2)"),
    ]


@dataclass
class Lead:
    degree: int
    form: Poly


def verify_circuit(data, weight):
    target_ops=78 if weight=="V2" else 79
    target_degree=630 if weight=="V2" else 468
    require(data["witnesses"]==INPUTS,"Wrong independent coordinates")
    require(data["fixed_numerals"]==PORTS,"Wrong fixed ports")
    require(data["domain"]=="strictly positive integers","Wrong domain")
    rows=data["source"];known=set(INPUTS+PORTS);table={}
    for row in rows:
        require(len(row)==4,"Malformed source row")
        name,op,a,b=row
        require(name not in known,"Duplicate register")
        require(op in {"+","-","*"},"Non-polynomial operation")
        for value in (a,b):
            require(type(value) is int or isinstance(value,str) and value in known,"Unknown or forward operand")
        known.add(name);table[name]=(op,a,b)
    require(data["output"]=="N","Wrong output")
    live=set()
    def mark(name):
        if type(name) is int or name in live:return
        live.add(name)
        if name in table:
            _,a,b=table[name];mark(a);mark(b)
    mark("N")
    require(live==known,"Dead register, input, or fixed port")
    counts=dict(sorted(Counter(r[1] for r in rows).items()))
    require(len(rows)==target_ops==data["operations"],"Wrong live operation count")
    require(counts==data["operation_breakdown"],"Wrong operation breakdown")

    covered=set()
    for target,cuts,formula in checks_for(weight):
        ring=Ring(cuts);cache={x:ring.variable(x) for x in cuts}
        def expand(name):
            if type(name) is int:return ring.constant(name)
            if name in cache:return cache[name]
            require(name in table,"Unstated free variable in a polynomial cut")
            covered.add(name)
            op,a,b=table[name];a,b=expand(a),expand(b)
            result=a+b if op=="+" else a-b if op=="-" else a*b
            cache[name]=result;return result
        require(expand(target)==expression(formula,ring),"Free polynomial identity failed: "+target)
    require(covered==set(table),"Not every actual register is covered by an exact cut identity")

    ring=Ring(INPUTS+PORTS)
    leading={x:Lead(1 if x in INPUTS else 0,ring.variable(x)) for x in INPUTS+PORTS}
    def get(x):return Lead(0,ring.constant(x)) if type(x) is int else leading[x]
    for name,op,a,b in rows:
        a,b=get(a),get(b)
        if op=="*":
            result=Lead(a.degree+b.degree,a.form*b.form)
        elif a.degree==b.degree:
            result=Lead(a.degree,a.form+b.form if op=="+" else a.form-b.form)
        elif a.degree>b.degree:
            result=a
        else:
            result=Lead(b.degree,b.form if op=="+" else -b.form)
        require(bool(result.form.terms),"Full leading cancellation requires a lower-degree refinement")
        leading[name]=result
    require(leading["N"].degree==target_degree==data["exact_degree"],"Wrong attained global degree")
    expected=("16384*(beta*J)**382*w**46*s**112*i**20*(eta+zeta)**64*(T+alpha)**4*(beta*J-F-alpha)**2"
              if weight=="V2" else
              "-1024*(beta*J)**288*w**34*s**84*i**14*(eta+zeta)**46*(T+alpha)**2")
    require(leading["N"].form==expression(expected,ring),"Wrong entire leading homogeneous form")
    mon=ring.zero
    powers=({"beta":382,"J":382,"w":46,"s":112,"i":20,"eta":64,"T":4,"F":2}
            if weight=="V2" else {"beta":288,"J":288,"w":34,"s":84,"i":14,"eta":46,"T":2})
    mon=tuple(powers.get(x,0) for x in ring.names)
    coefficient=16384 if weight=="V2" else -1024
    require(leading["N"].form.terms.get(mon)==coefficient,"Missing exact nonzero monomial coefficient")
    return {"operations":target_ops,"operation_breakdown":counts,"degree":target_degree,
            "independent_inputs":len(INPUTS),"fixed_ports":len(PORTS),
            "exact_cut_identities":len(checks_for(weight)),"all_registers_covered":len(covered),
            "leading_terms":len(leading["N"].form.terms),
            "nonzero_coefficient":str(coefficient)+"*beta^"+str(powers["beta"]),
            "register_degrees":{n:leading[n].degree for n in ["q","X","Y","c","Am1","Delta","Dtau","U","DpI2","Fsqr","Q","Dg","cTR","V","Mtot","Bt","Znum","RG","N"]}}


def mutation_checks(data,weight):
    failures=[]
    cases=[("Y","operand",2,"q2"),("Fsqr","operator",1,"-"),
           ("brk","operator",1,"-"),("Znum","operator",1,"+"),
           ("Q","operand",2,"U"),("N","operator",1,"-"),
           ("e","operand",3,2),("Y2","operand",3,"q")]
    for register,kind,index,value in cases:
        altered=deepcopy(data)
        row=next(r for r in altered["source"] if r[0]==register)
        row[index]=value
        altered["operation_breakdown"]=dict(sorted(Counter(r[1] for r in altered["source"]).items()))
        try:verify_circuit(altered,weight)
        except (ValueError,KeyError):failures.append(register+"/"+kind)
        else:raise ValueError("Accepted actual algebraic corruption: "+register)
    return failures


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output")
    args=parser.parse_args()
    pins=json.loads((ROOT/"SOURCE_PINS.json").read_text())
    for pin in pins:
        require(hashlib.sha256((ROOT/pin["file"]).read_bytes()).hexdigest()==pin["sha256"],"Pinned source differs: "+pin["file"])
    result={"source_files_authenticated":len(pins),"fixed_numerals":check_or_write(False),"equations":{}}
    for path,weight in [("equation78.json","V2"),("equation79.json","bV")]:
        data=json.loads((ROOT/path).read_text())
        for meta in data["coefficient_binding"]["ports"].values():
            stored=(ROOT/"coefficients"/meta["file"]).read_bytes()
            raw=gzip.decompress(stored)
            require(hashlib.sha256(stored).hexdigest()==meta["gzip_sha256"],"Compressed coefficient mismatch")
            require(hashlib.sha256(raw).hexdigest()==meta["raw_sha256"],"Raw coefficient mismatch")
        rec=verify_circuit(data,weight)
        rec["rejected_actual_corruptions"]=mutation_checks(data,weight)
        rec["sha256"]=hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
        result["equations"][path]=rec
    result["status"]="PASS"
    result["scope"]="Exact finite algebra, literal circuit, fixed-numeral and degree verification; the unbounded equivalence is proved in PROOF.md and its named ordinary dependencies."
    text=json.dumps(result,indent=2)+"\n"
    if args.output:Path(args.output).write_text(text)
    print(text,end="")


if __name__ == "__main__":main()
