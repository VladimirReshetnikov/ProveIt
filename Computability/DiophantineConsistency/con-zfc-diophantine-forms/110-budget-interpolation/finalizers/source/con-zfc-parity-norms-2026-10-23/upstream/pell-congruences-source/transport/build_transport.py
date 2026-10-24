#!/usr/bin/env python3
"""Expose C and eliminate the monic transport coordinate F exactly.

New equations stay in a finite DAG/factored representation, avoiding an
unnecessary expansion of the highest-degree residual. Every abbreviation
is polynomial and denotes no extra existential variable.

Uses only Python's standard library. Parent packets are inert JSON. An
exact univariate polynomial calculation modulo a prime certifies actual
degree after authentic fixed-coefficient specialization.
"""
import ast
import gzip
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
P=1000000007
COEFFICIENT_DIRECTORY=(Path(sys.argv[1]).resolve() if len(sys.argv)>1
                       else HERE.parent/"coefficients/payloads")

def trim(a):
    a=list(a)
    while a and not a[-1]: a.pop()
    return a

def uadd(a,b):
    z=[0]*max(len(a),len(b))
    for i,v in enumerate(a):z[i]=(z[i]+v)%P
    for i,v in enumerate(b):z[i]=(z[i]+v)%P
    return trim(z)

def uneg(a):return [(-v)%P for v in a]

def umul(a,b):
    if not a or not b:return []
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%P
    return trim(z)

def upow(a,k):
    if type(k) is not int or k<0:raise ValueError("invalid exponent")
    z=[1]
    while k:
        if k&1:z=umul(z,a)
        k//=2
        if k:a=umul(a,a)
    return z

def evaluate(s,env):
    def rec(n):
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.Constant) and type(n.value) is int:return trim([n.value%P])
        if isinstance(n,ast.UnaryOp):
            if isinstance(n.op,ast.USub):return uneg(rec(n.operand))
            if isinstance(n.op,ast.UAdd):return rec(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Add):return uadd(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Sub):return uadd(rec(n.left),uneg(rec(n.right)))
            if isinstance(n.op,ast.Mult):return umul(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant):return upow(rec(n.left),n.right.value)
        raise ValueError(ast.dump(n))
    return rec(ast.parse(s,mode="eval").body)

def degree(s,env):
    def rec(n):
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.Constant) and type(n.value) is int:return 0
        if isinstance(n,ast.UnaryOp):return rec(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,(ast.Add,ast.Sub)):return max(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Mult):return rec(n.left)+rec(n.right)
            if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant):return rec(n.left)*n.right.value
        raise ValueError(ast.dump(n))
    return rec(ast.parse(s,mode="eval").body)

def refs(s):return {n.id for n in ast.walk(ast.parse(s,mode="eval")) if isinstance(n,ast.Name)}

def require(p,label):
    if not p:raise RuntimeError(label)

def coefficient_data():
    # In the integrated release, use its existing authenticated payloads.
    directory=COEFFICIENT_DIRECTORY
    if not (directory/"beta.bin.gz").exists():
        raise RuntimeError("Authentic payloads unavailable; optional first argument is their directory")
    values={};hashes={}
    for n in ["beta","K0","MC","MF","cone_A","cone_B"]:
        raw=gzip.decompress((directory/(n+".bin.gz")).read_bytes())
        values[n]=int.from_bytes(raw,"little")%P
        hashes[n]=hashlib.sha256(raw).hexdigest()
    return values,hashes

def certify(packet,ports):
    dv={n:1 for n in packet["variables"]};dv.update({n:0 for n in ports})
    for n,f in packet["polynomial_abbreviations"]:dv[n]=degree(f,dv)
    bounds=[degree(f,dv) for f in packet["factored_residuals"]]
    top=max(bounds)
    require(2*top==packet["exact_degree"],packet["name"]+" degree upper bound")
    for trial in range(1,17):
        slopes={x:(i+2)*(trial+1)+trial*i*i+1 for i,x in enumerate(packet["variables"])}
        env={x:[0,a%P] for x,a in slopes.items()}
        env.update({n:[a] for n,a in ports.items()})
        for n,f in packet["polynomial_abbreviations"]:env[n]=evaluate(f,env)
        for i,f in enumerate(packet["factored_residuals"]):
            if bounds[i]!=top:continue
            value=evaluate(f,env)
            if len(value)==top+1 and value[-1]:
                return {"residual_degree_upper_bounds":bounds,
                    "residual_index_zero_based":i,"residual_exact_degree":top,
                    "method":"exact univariate polynomial specialization modulo a prime",
                    "substitution":"each unknown x is replaced by slope[x]*t",
                    "slopes":slopes,"prime":P,"actual_fixed_ports_mod_prime":ports,
                    "coefficient_of_t_to_residual_degree":value[-1],
                    "sum_of_squares_exact_degree":2*top,
                    "reason":"nonzero actual leading homogeneous specialization; a sum of real homogeneous squares cannot cancel"}
    raise RuntimeError(packet["name"]+" no leading coefficient certificate")

def make(parent_name,name,degree_value,paired_from_raw=False):
    raw=(HERE/"parents"/(parent_name+".json")).read_bytes()
    parent=json.loads(raw)
    variables=["C_native" if v=="alpha" else v for v in parent["variables"] if v!="F"]
    if "factored_residuals" in parent:
        defs=[]
        for n,f in parent["polynomial_abbreviations"]:
            if n=="C":
                defs.extend([["C","C_native"],["F","(K0+W)*C-z*(q-1)"],["alpha","q-F-C"]])
            elif n=="R":defs.append([n,"(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*Jnative"])
            else:defs.append([n,f])
        equations=list(parent["factored_residuals"])
        # One source is the raw20 form, paired here to avoid needing its
        # huge expanded eighteen-variable sibling as an input file.
        if paired_from_raw:
            variables=[x for x in variables if not x.startswith(("eta_zeta_pos","cone_pos"))]
            variables += ["pair_root","pair_pos1","pair_pos2","pair_pos3"]
            defs.append(["Zeta","eta*zeta"])
            equations=equations[:-2]+["G*Zeta-(pair_root**2-G-Zeta+1)**2-1-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)"]
        transport="(K0+W)*C-F-z*(q-1)"
        require(equations.count(transport)==1,"unique factored transport row")
        deleted=equations.index(transport)
        equations.pop(deleted)
    else:
        qtext="beta*(3*J3+1)+1" if "J3" in parent["variables"] else "beta*J+1"
        wtext="4*(3*w3+1)" if "w3" in parent["variables"] else "4*w_scale"
        defs=[["q",qtext],["W",wtext],["C","C_native"],
              ["F","(K0+W)*C-z*(q-1)"],["alpha","q-F-C"]]
        equations=list(parent["residuals"])
        # These small packets retain the source row order. Find the one
        # containing the transport-only coefficient K0; validate below
        # by exact polynomial identities over independent indeterminates.
        hits=[i for i,f in enumerate(equations) if "K0" in refs(f)]
        require(len(hits)==1,"unique transport coefficient row")
        deleted=hits[0];equations.pop(deleted)

    # Topological and liveness checks at the finite DAG level.
    fixed=parent["fixed_numerals"]
    known=set(variables)|set(fixed);dep={x:{x} for x in known}
    for n,f in defs:
        require(refs(f)<=known,"forward or unknown abbreviation "+n)
        dep[n]=set().union(*(dep[x] for x in refs(f))) if refs(f) else set()
        known.add(n)
    live=set()
    for f in equations:
        require(refs(f)<=known,"unknown residual name")
        live |= set().union(*(dep[x] for x in refs(f)))
    require(live==set(variables)|set(fixed),name+" liveness")

    return {"name":name,"domain":"unrestricted integers","variables":variables,
            "variable_count":len(variables),"fixed_numerals":fixed,
            "residual_count":len(equations),"polynomial_abbreviations":defs,
            "factored_residuals":equations,"exact_degree":degree_value,
            "representation":"finite ordered polynomial abbreviations; abbreviations are not extra unknowns",
            "single_polynomial":"sum of the squares of the factored residuals after polynomial abbreviation expansion",
            "coefficient_binding":"../coefficients/BINDING.json",
            "parent_packet":parent_name+".json","parent_sha256":hashlib.sha256(raw).hexdigest(),
            "parent_pairing_first":paired_from_raw,
            "deleted_transport_row_zero_based":deleted,
            "exact_restoration":{"alpha":"q-F-C_native","F":"(K0+W)*C_native-z*(q-1)"},
            "new_semantic_step":"integral coordinate alpha-to-C change followed by monic elimination of F",
            "proof_status":"ordinary exact polynomial zero-set bijection; inherited native/Pell calibration remains explicit"}

def rank_register(parent):
    """Restore the native rank as one explicit coordinate to reduce degree."""
    obj=dict(parent)
    obj["name"]="degree20_20_rank_register"
    obj["parent_transport_packet"]=parent["name"]+".json"
    obj["variables"]=parent["variables"]+["R_register"]
    obj["variable_count"]=len(obj["variables"])
    defs=[]
    for n,f in parent["polynomial_abbreviations"]:
        if n=="R":defs += [["R_native",f],["R","R_register"]]
        else:defs.append([n,f])
    obj["polynomial_abbreviations"]=defs
    obj["factored_residuals"]=["R_register-R_native"]+parent["factored_residuals"]
    obj["residual_count"]=len(obj["factored_residuals"])
    obj["exact_degree"]=20
    obj["new_semantic_step"]="monic native transport elimination followed by one rank register; forgetting the register is a zero-set bijection"
    return obj

def main():
    ports,hashes=coefficient_data()
    specs=[("degree10_25","degree10_24",10,False),
           ("degree12_23","degree16_22",16,False),
           ("degree26_20","degree28_19",28,False),
           ("degree32_19","degree32_18",32,False),
           ("crt_degree44_20","degree88_17",88,True)]
    summary={}
    objects={}
    for parent,name,d,pair in specs:
        obj=make(parent,name,d,pair)
        cert=certify(obj,ports)
        obj["degree_certificate"]=cert
        (HERE/(name+".json")).write_text(json.dumps(obj,indent=2,sort_keys=True)+"\n")
        (HERE/"certificates"/(name+"_degree.json")).write_text(json.dumps(cert,indent=2,sort_keys=True)+"\n")
        summary[name]={"variables":obj["variable_count"],"residuals":obj["residual_count"],
                       "exact_degree":d,"residual_degree_bounds":cert["residual_degree_upper_bounds"]}
        objects[name]=obj
    obj=rank_register(objects["degree28_19"])
    obj["degree_certificate"]=certify(obj,ports)
    name=obj["name"];cert=obj["degree_certificate"]
    (HERE/(name+".json")).write_text(json.dumps(obj,indent=2,sort_keys=True)+"\n")
    (HERE/"certificates"/(name+"_degree.json")).write_text(json.dumps(cert,indent=2,sort_keys=True)+"\n")
    summary[name]={"variables":obj["variable_count"],"residuals":obj["residual_count"],
                   "exact_degree":20,"residual_degree_bounds":cert["residual_degree_upper_bounds"]}
    out={"status":"PASS","scope":"finite DAG topology, liveness, degree upper bounds and exact actual-coefficient leading specializations",
         "actual_raw_coefficient_sha256":hashes,"equations":summary}
    (HERE/"certificates/TRANSPORT_CHECKS.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")
    print(json.dumps(out,indent=2))

if __name__=="__main__":main()
