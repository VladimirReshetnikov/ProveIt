#!/usr/bin/env python3
"""Independent audit without importing the builder or expanding large rows.

Exact local polynomial identities and a strict structural comparison prove
the global substitution. The degree certificate is independently checked
by finite differences, not the builder's polynomial-coefficient algorithm.
"""
import ast
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
COEFFICIENT_DIRECTORY=(Path(sys.argv[1]).resolve() if len(sys.argv)>1
                       else HERE.parent/"coefficients/payloads")
CHECKS=[]

def require(p,label):
    if not p:raise RuntimeError(label)
    CHECKS.append(label)

def canon(s):return ast.dump(ast.parse(s,mode="eval"),include_attributes=False)

# A small exact ring for the local identities, independent of the builder.
def add(a,b):
    c=dict(a)
    for m,v in b.items():c[m]=c.get(m,0)+v
    return {m:v for m,v in c.items() if v}
def neg(a):return {m:-v for m,v in a.items()}
def mul(a,b):
    c={}
    for m,x in a.items():
        for n,y in b.items():
            k=tuple(sorted(m+n));c[k]=c.get(k,0)+x*y
    return {m:v for m,v in c.items() if v}
def exp(a,n):
    c={():1}
    for _ in range(n):c=mul(c,a)
    return c
def ring(s,env=None):
    env=env or {}
    def rec(n):
        if isinstance(n,ast.Name):return env.get(n.id,{(n.id,):1})
        if isinstance(n,ast.Constant) and type(n.value) is int:return {():n.value} if n.value else {}
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return neg(rec(n.operand))
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Add):return add(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Sub):return add(rec(n.left),neg(rec(n.right)))
            if isinstance(n.op,ast.Mult):return mul(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant):return exp(rec(n.left),n.right.value)
        raise ValueError(ast.dump(n))
    return rec(ast.parse(s,mode="eval").body)

def names(s):return {n.id for n in ast.walk(ast.parse(s,mode="eval")) if isinstance(n,ast.Name)}

def degree(s,env):
    def rec(n):
        if isinstance(n,ast.Constant):return 0
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp):return rec(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,(ast.Add,ast.Sub)):return max(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Mult):return rec(n.left)+rec(n.right)
            if isinstance(n.op,ast.Pow):return rec(n.left)*n.right.value
        raise ValueError(ast.dump(n))
    return rec(ast.parse(s,mode="eval").body)

def value(s,env,p):
    def rec(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return n.value%p
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -rec(n.operand)%p
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Add):return (rec(n.left)+rec(n.right))%p
            if isinstance(n.op,ast.Sub):return (rec(n.left)-rec(n.right))%p
            if isinstance(n.op,ast.Mult):return rec(n.left)*rec(n.right)%p
            if isinstance(n.op,ast.Pow):return pow(rec(n.left),n.right.value,p)
        raise ValueError(ast.dump(n))
    return rec(ast.parse(s,mode="eval").body)

def payload_directory():
    if (COEFFICIENT_DIRECTORY/"beta.bin.gz").exists():return COEFFICIENT_DIRECTORY
    raise RuntimeError("Authentic payloads unavailable; optional first argument is their directory")

def check_packet(file,receipt):
    obj=json.loads(file.read_text());name=obj["name"]
    raw=(HERE/"parents"/obj["parent_packet"]).read_bytes()
    require(hashlib.sha256(raw).hexdigest()==obj["parent_sha256"],name+" parent hash")
    par=json.loads(raw)
    expected_vars=["C_native" if x=="alpha" else x for x in par["variables"] if x!="F"]
    paired=obj["parent_pairing_first"]
    if paired:
        expected_vars=[x for x in expected_vars if not x.startswith(("cone_pos","eta_zeta_pos"))]
        expected_vars += ["pair_root","pair_pos1","pair_pos2","pair_pos3"]
    rank_register="parent_transport_packet" in obj
    if rank_register:expected_vars.append("R_register")
    require(expected_vars==obj["variables"],name+" exact coordinate list")
    require(len(expected_vars)==obj["variable_count"],name+" count")
    require(obj["fixed_numerals"]==par["fixed_numerals"],name+" unchanged six fixed ports")

    if "factored_residuals" in par:
        expected=[]
        for n,f in par["polynomial_abbreviations"]:
            if n=="C":
                expected += [["C","C_native"],["F","(K0+W)*C-z*(q-1)"],["alpha","q-F-C"]]
            elif n=="R":expected.append([n,"(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*Jnative"])
            else:expected.append([n,f])
        rr=list(par["factored_residuals"])
        if paired:
            require(ring(rr[-2])==ring("eta*zeta-1-eta_zeta_pos1**2-eta_zeta_pos2**2-eta_zeta_pos3*(eta_zeta_pos3+1)"),name+" old Z guard")
            require(ring(rr[-1])==ring("G-1-cone_pos1**2-cone_pos2**2-cone_pos3*(cone_pos3+1)"),name+" old G guard")
            expected.append(["Zeta","eta*zeta"])
            rr=rr[:-2]+["G*Zeta-(pair_root**2-G-Zeta+1)**2-1-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)"]
        hits=[i for i,s in enumerate(rr) if canon(s)==canon("(K0+W)*C-F-z*(q-1)")]
        require(len(hits)==1,name+" unique transport row")
        delete=hits[0];rr.pop(delete)
    else:
        expected=[["q","beta*(3*J3+1)+1"],["W","4*(3*w3+1)"],["C","C_native"],
                  ["F","(K0+W)*C-z*(q-1)"],["alpha","q-F-C"]]
        rr=list(par["residuals"])
        hits=[i for i,s in enumerate(rr) if "K0" in names(s)]
        require(len(hits)==1,name+" unique coefficient-bearing row")
        delete=hits[0]
        q=ring("beta*(3*J3+1)+1");W=ring("4*(3*w3+1)")
        F=ring("(K0+W)*C_native-z*(q-1)",{"q":q,"W":W})
        alpha=ring("q-F-C_native",{"q":q,"F":F})
        require(not ring(rr[delete],{"F":F,"alpha":alpha}),name+" exact expanded transport zero")
        rr.pop(delete)
    if rank_register:
        renamed=[]
        for n,f in expected:
            if n=="R":renamed += [["R_native",f],["R","R_register"]]
            else:renamed.append([n,f])
        expected=renamed
        rr=["R_register-R_native"]+rr
    require(len(expected)==len(obj["polynomial_abbreviations"]),name+" abbreviation count")
    for (a,b),(c,d) in zip(expected,obj["polynomial_abbreviations"]):
        require(a==c and canon(b)==canon(d),name+" exact abbreviation "+a)
    require([canon(s) for s in rr]==[canon(s) for s in obj["factored_residuals"]],name+" all retained residuals unchanged")
    require(delete==obj["deleted_transport_row_zero_based"],name+" deleted row index")
    require(len(rr)==obj["residual_count"],name+" residual count")

    # Independent degree and actual coefficient proof by finite differences.
    cert=obj["degree_certificate"];p=cert["prime"]
    require(p==1000000007,name+" fixed audit prime")
    payloads=payload_directory();ports={}
    for x in obj["fixed_numerals"]:
        raw=gzip.decompress((payloads/(x+".bin.gz")).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==receipt["actual_raw_coefficient_sha256"][x],name+" actual raw port "+x)
        ports[x]=int.from_bytes(raw,"little")%p
    require(ports==cert["actual_fixed_ports_mod_prime"],name+" actual port residues")
    dd={x:1 for x in obj["variables"]};dd.update({x:0 for x in ports})
    for n,f in obj["polynomial_abbreviations"]:dd[n]=degree(f,dd)
    bounds=[degree(f,dd) for f in rr]
    require(bounds==cert["residual_degree_upper_bounds"],name+" independent degree bounds")
    h=cert["residual_exact_degree"];row=cert["residual_index_zero_based"]
    require(h==max(bounds) and 2*h==obj["exact_degree"],name+" maximum degree")
    values=[]
    for t in range(h+1):
        env={x:cert["slopes"][x]*t%p for x in obj["variables"]};env.update(ports)
        for n,f in obj["polynomial_abbreviations"]:env[n]=value(f,env,p)
        values.append(value(rr[row],env,p))
    for _ in range(h):values=[(b-a)%p for a,b in zip(values,values[1:])]
    lead=values[0]*pow(math.factorial(h)%p,p-2,p)%p
    require(lead!=0 and lead==cert["coefficient_of_t_to_residual_degree"],name+" finite-difference leading coefficient")
    return {"variables":obj["variable_count"],"residuals":obj["residual_count"],"degree":obj["exact_degree"],
            "degree_verified_by":"independent finite-difference identity"}

def main():
    C=ring("C");F=ring("(K0+W)*C-z*(q-1)")
    alpha=ring("q-F-C",{"F":F})
    require(ring("q-F-alpha",{"F":F,"alpha":alpha})==C,"coordinate change exact inverse")
    require(not ring("(K0+W)*C-F-z*(q-1)",{"F":F}),"monic transport exact zero")
    require(ring("((q-1)*(q-F)+alpha)*(q**2-1)+(MC+q*MF)*Jnative",{"alpha":ring("q-F-C")})==
            ring("(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*Jnative"),"native rank simplification exact identity")
    receipt=json.loads((HERE/"certificates/TRANSPORT_CHECKS.json").read_text())
    metrics={p.stem:check_packet(p,receipt) for p in sorted(HERE.glob("degree*.json"))}
    out={"status":"PASS","checks":len(CHECKS),"metrics":metrics,"check_labels":CHECKS,
         "scope":"Exact local identities and strict global DAG transformation; actual degree certified independently using finite differences. Inherited native/Pell proofs remain separate."}
    (HERE/"certificates/INDEPENDENT_TRANSPORT_AUDIT.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"PASS","checks":len(CHECKS),"metrics":metrics},indent=2))

if __name__=="__main__":main()
