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


def checks_for(mode,weight):
    zweight="V**2" if weight=="V2" else "cTR*V"
    result = [
      ("q",["beta","J"],"beta*J+1"),
      ("Y",["q","s"],"q**2*s" if mode=="partial" else "q**3*s"),
      ("C",["q","F","alpha"],"q-F-alpha"),
      ("X",["w","q"],"w*q"),
      ("k",["eta","zeta"],"eta+zeta"),
      ("c",["k","Y","eta"],"k*Y+eta"),
      ("Am1",["Y","X"],"Y*(X+1)"),
      ("Hp",["Am1"],"4*Am1-1"),
      ("Delta",["Am1"],"Am1*(Am1+2)"),
      ("V0",["X","Y"],"X*Y**2"),
      ("D",["X","Y","q"],{"xy":"X*Y","q4":"q**4","partial":"q**3*Y"}[mode]),
      ("Dtau",["V0","k"],"1+V0*(V0+1)*k**2"),
      ("R",["bJ","q","F","alpha","MC","MF","J"],"(bJ*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*J"),
      ("e",["k","R"],"k-R-1"),
      ("Bt",["K0","w","C","F"],"(K0+w)*C-F"),
      ("U",["i","c"],"i*c**2"),
      ("DpI2",["Delta","U","Dtau"],"Delta*U**2*Dtau"),
      ("Df",["DpI2"],"1+DpI2"),
      ("Fsqr",["DpI2"],"1+4*DpI2*(1+DpI2)"),
      ("Q",["Delta","DpI2"],"4*Delta*DpI2*(1+DpI2)"),
      ("cTR",["c","T","R"],"c*T-R"),
      ("V",["Fsqr","cTR","c"],"Fsqr*cTR-c"),
      ("Kpos",["X","c"],"X*(3*c-2*X)+2"),
      ("Mtot",["bJ","D","Hp"],"bJ*D*Hp"),
      ("Znum",["bJ","D","Hp","n","Bt","Kpos","e","V","cTR","Y"],
       "bJ*D*(Hp*(n-("+zweight+")*Bt)+Kpos)"+("+Hp*(bJ*(Y**2-e)-D*Bt)" if mode=="partial" else "-Hp*(D*Bt+bJ*e)")),
      ("Dg",["Dtau","Df"],"Dtau*Df"),
      ("RG",["Mtot","Dg"],"Mtot**2*Dg"),
      ("N",["Q","Znum","Mtot","Dg","V"],"Q*(Znum**2-Mtot**2*Dg*V**2)+(Mtot**2*Dg-Znum**2)"),
    ]

    return result


@dataclass
class Lead:
    degree: int
    form: Poly


def verify_circuit(data, mode, weight):
    target_ops={"xy":77,"q4":78,"partial":79}[mode]+(weight=="bV")
    target_degree={"xy":(626,464),"q4":(622,460),"partial":(518,384)}[mode][weight=="bV"]
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
    for target,cuts,formula in checks_for(mode,weight):
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
    qpow,wexp,sexp=({"xy":(378,48,110),"q4":(378,46,108),"partial":(272,46,110)}[mode]
                        if weight=="V2" else {"xy":(284,36,82),"q4":(284,34,80),"partial":(206,34,82)}[mode])
    coefficient=16384 if weight=="V2" else -1024
    iexp,kexp,texp=(20,64,4) if weight=="V2" else (14,46,2)
    expected=f"{coefficient}*(beta*J)**{qpow}*w**{wexp}*s**{sexp}*i**{iexp}*(eta+zeta)**{kexp}*T**{texp}"
    if weight=="V2":expected+="*(beta*J-F-alpha)**2"
    require(leading["N"].form==expression(expected,ring),"Wrong entire leading homogeneous form")
    powers={"beta":qpow,"J":qpow,"w":wexp,"s":sexp,"i":iexp,"eta":kexp,"T":texp}
    if weight=="V2":powers["F"]=2
    mon=tuple(powers.get(x,0) for x in ring.names)
    require(leading["N"].form.terms.get(mon)==coefficient,"Missing exact nonzero monomial coefficient")
    return {"operations":target_ops,"operation_breakdown":counts,"degree":target_degree,
            "independent_inputs":len(INPUTS),"fixed_ports":len(PORTS),
            "exact_cut_identities":len(checks_for(mode,weight)),"all_registers_covered":len(covered),
            "leading_terms":len(leading["N"].form.terms),
            "nonzero_coefficient":str(coefficient)+"*beta^"+str(powers["beta"]),
            "register_degrees":{n:leading[n].degree for n in ["q","X","Y","c","Am1","Delta","Dtau","U","DpI2","Fsqr","Q","Dg","cTR","V","Mtot","Bt","Znum","RG","N"]}}


def mutation_checks(data,mode,weight):
    failures=[]
    cases=[("Y","operand",3,"n"),("Fsqr","operator",1,"-"),
           ("brk","operator",1,"+" if mode=="partial" else "-"),("Znum","operator",1,"-" if mode=="partial" else "+"),
           ("Q","operand",2,"U"),("N","operator",1,"-"),
           ("e","operand",3,2),("D","operand",3,3)]
    for register,kind,index,value in cases:
        altered=deepcopy(data)
        row=next(r for r in altered["source"] if r[0]==register)
        row[index]=value
        altered["operation_breakdown"]=dict(sorted(Counter(r[1] for r in altered["source"]).items()))
        try:verify_circuit(altered,mode,weight)
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
    for mode in ["xy","q4","partial"]:
      for weight in ["V2","bV"]:
        path=mode+("_v2.json" if weight=="V2" else "_bv.json")
        data=json.loads((ROOT/path).read_text())
        for meta in data["coefficient_binding"]["ports"].values():
            stored=(ROOT/"coefficients"/meta["file"]).read_bytes()
            raw=gzip.decompress(stored)
            require(hashlib.sha256(stored).hexdigest()==meta["gzip_sha256"],"Compressed coefficient mismatch")
            require(hashlib.sha256(raw).hexdigest()==meta["raw_sha256"],"Raw coefficient mismatch")
        rec=verify_circuit(data,mode,weight)
        rec["rejected_actual_corruptions"]=mutation_checks(data,mode,weight)
        rec["sha256"]=hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
        result["equations"][path]=rec
    result["status"]="PASS"
    result["scope"]="Exact finite algebra, literal circuit, fixed-numeral and degree verification; the unbounded equivalence is proved in PROOF.md and its named ordinary dependencies."
    text=json.dumps(result,indent=2)+"\n"
    if args.output:Path(args.output).write_text(text)
    print(text,end="")


if __name__ == "__main__":main()
