#!/usr/bin/env python3
"""Derive a fixed-blank-input polynomial circuit from ProveIt's complete84.

Only JSON data are read from the repository; no historical Python is imported.
The returned object is an arithmetic circuit, not a declaration that arbitrary
four-constant assignments are valid program encodings.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

PARENT_SHA256 = "8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf"
PARENT_REL = "Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete84_scaled_strong_output.json"
REPO_COMMIT = "cdd582bec13f908df3711fa9e05d1ddac368a5db"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def canonical_hash(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def evaluate(source, supplied):
    values = dict(supplied)
    def get(x):
        return x if type(x) is int else values[x]
    for name, op, a, b in source:
        av, bv = get(a), get(b)
        values[name] = av + bv if op == "+" else av - bv if op == "-" else av * bv
    return values


def ledger(source, free, outputs):
    known = set(free)
    producers = {}
    counts = Counter()
    for gate in source:
        require(len(gate) == 4, "invalid gate")
        name, op, a, b = gate
        require(name not in known, f"duplicate register {name}")
        require(op in ("+", "-", "*"), "invalid operation")
        for x in (a, b):
            require(type(x) is int or isinstance(x, str) and x in known, f"unknown operand {x}")
        known.add(name)
        producers[name] = (a, b)
        counts["M" if op == "*" else "A"] += 1
    needed = set(outputs)
    for name, _, a, b in reversed(source):
        if name in needed:
            needed.update(x for x in (a, b) if isinstance(x, str))
    require(set(producers) <= needed, "dead arithmetic gate")
    require(set(free) <= needed, "dead supplied port")
    return {"operations":len(source),"M":counts["M"],"A":counts["A"],"all_gates_live":True,"all_ports_live":True}


def build(parent):
    p = parent["packet"]
    drop = {
        "gamma_sum", "q_minus_FZ", "C_after_alpha", "scaled_t", "marked_rhs",
        "W", "odd_index", "index_product", "index_rhs", "difference_multiple",
        "exponent_partial", "modulus_multiple", "exponent_rhs", "mu2", "kappa2",
        "scaled_kappa2", "norm_input", "norm_triple",
    }
    alias = {"gamma_sum":"gamma", "q_minus_FZ":"alpha", "marked_rhs":"C", "norm_triple":"norm_pair"}
    source = []
    for name, op, a, b in p["source"]:
        if name == "marked_rhs":
            source.append(["C", "-", "q_minus_F", "alpha"])
        if name not in drop:
            source.append([name,op,alias.get(a,a),alias.get(b,b)])
    require(len(drop) == 18 and len(source) == 67, "incorrect gate transformation")
    removed_witnesses = {"Z","delta","rho","sigma"}
    witnesses = [w for w in p["witnesses"] if w not in removed_witnesses] + ["gamma"]
    constants = ["Bm1", "Kconstant", "MC", "MF"]
    # Four numerical ports suffice once the marker and variable input are gone.
    factors = [f for f in p["factors"] if f != "norm_input"]
    out = {
        "name":"fixed_blank_67", "repository_commit":REPO_COMMIT,
        "parent_path":PARENT_REL, "parent_sha256":PARENT_SHA256,
        "witness_domain":"strictly positive integers", "witnesses":witnesses,
        "fixed_numerals":constants, "ordinary_input":None,
        "source":source, "output":"polynomial", "factors":factors,
        "factor_exact_degrees":[22,18,60,7,2,46], "exact_degree":155,
        "uniform_leading_form":"-8*Q^91*h*gamma*i^4*(eta+zeta)^13*w^13*s^26*auxiliary_quotient^2*f^2*(w*(Q-F-alpha)-transport_quotient*Q), Q=Bm1*Jrep",
        "uniform_nonzero_coefficient":"8*Bm1^92",
        "uniform_nonzero_monomial":"Jrep^92*h*gamma*i^4*eta^13*w^13*s^26*auxiliary_quotient^2*f^2*transport_quotient",
        "ledger":ledger(source, witnesses+constants, ["polynomial"]),
        "scope":"Fixed blank computation; valid modified native compiler with impossible End selector and a genuine Start; source algebra verified separately from compiler semantics.",
        "transformation":{"deleted_registers":sorted(drop),"added_registers":["C"],"aliases":alias},
    }
    require(len(witnesses)==15, "witness count")
    out["source_sha256"]=canonical_hash(source)
    return out


def reduce_auxiliary(packet):
    out=json.loads(json.dumps(packet))
    source=[]
    for gate in out["source"]:
        if gate[0]=="L17":
            source.append(["auxiliary_reduced_coefficient","-","scaled_f_square","A"])
            source.append(["L17","*","auxiliary_reduced_coefficient","aux_square_gap"])
        else:
            source.append(gate)
    out.update(name="fixed_blank_68",source=source,exact_degree=123,
               factor_exact_degrees=[22,18,28,7,2,46],
               uniform_leading_form="-8*Q^71*h*gamma*i^2*(eta+zeta)^9*w^11*s^20*auxiliary_quotient^2*f^4*(w*(Q-F-alpha)-transport_quotient*Q), Q=Bm1*Jrep",
               uniform_nonzero_coefficient="8*Bm1^72",
               uniform_nonzero_monomial="Jrep^72*h*gamma*i^2*eta^9*w^11*s^20*auxiliary_quotient^2*f^4*transport_quotient",
               all_integer_zero_equivalence_to="fixed_blank_67")
    out["ledger"]=ledger(source,out["witnesses"]+out["fixed_numerals"],[out["output"]])
    out["source_sha256"]=canonical_hash(source)
    return out


def comparison_system(packet):
    targets=packet["factors"]
    needed=set(targets+["A"])
    source=[]
    for row in reversed(packet["source"]):
        if row[0] in needed:
            source.append(row)
            needed.update(x for x in row[2:] if isinstance(x,str))
    source.reverse()
    comparisons=[[name,"A" if name=="norm_strong" else 1] for name in targets]
    out={"name":"fixed_blank_system_"+str(len(source)),"source":source,
         "witness_domain":packet["witness_domain"],"witnesses":packet["witnesses"],
         "fixed_numerals":packet["fixed_numerals"],"comparisons":comparisons,
         "same_positive_zeros_as":packet["name"],"residual_exact_degrees":packet["factor_exact_degrees"],
         "ledger":ledger(source,packet["witnesses"]+packet["fixed_numerals"],targets+["A"]),
         "scope":"Six explicit equations; multiplication/addition counts exclude equality tests."}
    sos=list(source)
    for i,(a,b) in enumerate(comparisons):
        sos.append([f"residual_{i}","-",a,b])
        sos.append([f"square_{i}","*",f"residual_{i}",f"residual_{i}"])
    last="square_0"
    for i in range(1,len(comparisons)):
        sos.append([f"sum_{i}","+",last,f"square_{i}"])
        last=f"sum_{i}"
    out["sum_of_squares"]={"source":sos,"output":last,"exact_degree":2*max(packet["factor_exact_degrees"]),
        "ledger":ledger(sos,packet["witnesses"]+packet["fixed_numerals"],[last])}
    return out


def integer_lift(packet,signed_square_coordinates=False):
    # Legendre's theorem applied to 4*n+1 proves surjectivity of
    # a^2+b^2+c(c+1) from Z^3 onto N. Every summand is nonnegative.
    source=[]
    witnesses=[]
    signed={"tau_root","y_aux"} if signed_square_coordinates else set()
    for name in packet["witnesses"]:
        if name in signed:
            witnesses.append(name)
            continue
        a,b,c=(name+suffix for suffix in ("_a","_b","_c"))
        witnesses.extend((a,b,c))
        source.extend([
            [name+"_a2","*",a,a],[name+"_b2","*",b,b],
            [name+"_c1","+",c,1],[name+"_cc1","*",c,name+"_c1"],
            [name+"_ab","+",name+"_a2",name+"_b2"],
            [name+"_sum","+",name+"_ab",name+"_cc1"],
            [name,"+",name+"_sum",1]])
    source.extend(packet["source"])
    return {"name":packet["name"]+("_over_Z41" if signed else "_over_Z"),"witness_domain":"all integers","witnesses":witnesses,
            "fixed_numerals":packet["fixed_numerals"],"source":source,"output":packet["output"],
            "exact_degree":2*packet["exact_degree"],"substitution":"x=1+x_a^2+x_b^2+x_c*(x_c+1)",
            "unrestricted_square_coordinates":sorted(signed),
            "ledger":ledger(source,witnesses+packet["fixed_numerals"],[packet["output"]]),
            "scope":"Unrestricted-integer form, with the domain-enforcement gate cost included."}


def check_variants(base,system,integer):
    rng=random.Random(6745)
    for _ in range(32):
        inputs={n:rng.randrange(-4,7) for n in integer["witnesses"]}
        for n in integer["unrestricted_square_coordinates"]:
            inputs[n]=rng.choice((-5,-3,-1,1,2,4))
        inputs.update({n:v for n,v in zip(base["fixed_numerals"],(31,127,10,45))})
        positive={n:abs(inputs[n]) if n in integer["unrestricted_square_coordinates"] else 1+inputs[n+"_a"]**2+inputs[n+"_b"]**2+inputs[n+"_c"]*(inputs[n+"_c"]+1) for n in base["witnesses"]}
        require(all(v>0 for v in positive.values()),"integer lift positivity")
        positive.update({n:inputs[n] for n in base["fixed_numerals"]})
        bv=evaluate(base["source"],positive)
        iv=evaluate(integer["source"],inputs)
        require(bv[base["output"]]==iv[integer["output"]],"integer substitution mismatch")
        sv=evaluate(system["sum_of_squares"]["source"],positive)
        expected=sum((bv[a]-(bv[b] if isinstance(b,str) else b))**2 for a,b in system["comparisons"])
        require(sv[system["sum_of_squares"]["output"]]==expected,"SOS mismatch")
    return {"integer_lift_cases":32,"six_equation_SOS_identity_cases":32,
            "scope":"Exact diagnostic evaluations; the report proves surjectivity and the full positive zero equivalence."}


def explicit_formula(v,reduced=False):
    J,F,al,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma = [v[n] for n in
        ("Jrep","F","alpha","transport_quotient","f","h","i","auxiliary_quotient","s","w","tau_root","eta","zeta","y_aux","gamma")]
    m,K,MC,MF=[v[n] for n in ("Bm1","Kconstant","MC","MF")]
    q=m*J+1; X=w*q; Y=s*q**3; E=X*Y; k=eta+zeta
    c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
    D=X+a*c+gamma*H; C=q-F-al
    R=(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J
    L=E*k*Y; V=c*(T*f-1)-R*f*f; S=(i*Delta*c*c)**2
    auxiliary_coefficient=Delta*(f*f-1) if reduced else S
    factors=[tau*tau-L*(L+k), D*D-Delta*c*c,
             auxiliary_coefficient*(V*V-y*y)+y*y, k-h*E-R,
             (K+w)*C+q-F-z*(q-1), Delta*f*f-S]
    P=1
    for u in factors: P*=u
    return P-Delta, factors


def degree_checks(packet):
    # Ring arithmetic in Z[t]/(prime) with every variable t and constants fixed.
    # This proves lower degree only; the uniform upper bound and leading-form
    # argument are written in the report. We test two independent generic lines.
    result=[]
    for prime,seed in ((1000000007,8371),(1000000009,8372)):
        rng=random.Random(seed)
        vals={n:[rng.randrange(1,13),rng.randrange(1,19)] for n in packet["witnesses"]}
        vals.update({n:[v] for n,v in zip(packet["fixed_numerals"],(31,127,10,45))})
        slopes={k:v[-1] for k,v in vals.items()}
        def get(x): return [x] if type(x) is int else vals[x]
        for name,op,a,b in packet["source"]:
            aa,bb=get(a),get(b)
            if op=="*":
                cc=[0]*(len(aa)+len(bb)-1)
                for i,x in enumerate(aa):
                    for j,y in enumerate(bb): cc[i+j]=(cc[i+j]+x*y)%prime
            else:
                cc=[0]*max(len(aa),len(bb))
                for i in range(len(cc)):
                    cc[i]=((aa[i] if i<len(aa) else 0)+(1 if op=="+" else -1)*(bb[i] if i<len(bb) else 0))%prime
            while len(cc)>1 and cc[-1]==0: cc.pop()
            vals[name]=cc
        degs=[len(vals[n])-1 for n in packet["factors"]]
        require(degs==packet["factor_exact_degrees"],f"factor degree mismatch {degs}")
        require(len(vals["polynomial"])-1==packet["exact_degree"],"degree not attained")
        Q=slopes["Bm1"]*slopes["Jrep"]
        tr=slopes["w"]*(Q-slopes["F"]-slopes["alpha"])-slopes["transport_quotient"]*Q
        exps=(91,4,13,13,26,2) if packet["name"]=="fixed_blank_67" else (71,2,9,11,20,4)
        eQ,ei,ek,ew,es,ef=exps
        lead=(-8*pow(Q,eQ,prime)*slopes["h"]*slopes["gamma"]*pow(slopes["i"],ei,prime)*
              pow(slopes["eta"]+slopes["zeta"],ek,prime)*pow(slopes["w"],ew,prime)*
              pow(slopes["s"],es,prime)*slopes["auxiliary_quotient"]**2*pow(slopes["f"],ef,prime)*tr)%prime
        require(lead==vals["polynomial"][-1],"uniform leading-form diagnostic mismatch")
        result.append({"modulus":prime,"seed":seed,"degree":packet["exact_degree"],"factor_degrees":degs,
                       "leading_coefficient":vals["polynomial"][-1]})
    return result


def check(packet):
    rng=random.Random(21567)
    cases=0
    for rational in (False,True):
        for _ in range(48):
            supplied={n:rng.randrange(-7,9) for n in packet["witnesses"]+packet["fixed_numerals"]}
            if rational:
                supplied={k:Fraction(v,rng.randrange(1,6)) for k,v in supplied.items()}
            vals=evaluate(packet["source"],supplied)
            P, fs=explicit_formula(supplied,reduced=packet["name"]=="fixed_blank_68")
            require(vals["polynomial"]==P,"independent formula mismatch")
            require([vals[n] for n in packet["factors"]]==fs,"independent factor mismatch")
            cases+=1
    # Exact finite arithmetic check of new pretyping bounds, including C=0.
    bounds_cases=0
    for q in range(16,81):
        for F in range(1,q):
            for al in (1,q-F):
                C=q-F-al
                if C<0: continue
                G=(q-1)*(q-F)+al
                require(q<=G<=q*q-q,"G bound")
                # extremal valid-mask bounds suffice for all inner masks.
                for M in (1,2*q*q-q-2):
                    R=G*(q*q-1)+M
                    require(3*q+1<R-2<q**4-4,"R bound")
                    bounds_cases+=1
    return {"independent_formula_cases":cases,"includes_signed_rational_tuples":True,
            "finite_pretyping_bound_cases":bounds_cases,"degree_diagnostics":degree_checks(packet),
            "scope":"Finite algebra diagnostics supplement the general proof; no gigantic accepting Pell witness has been materialized."}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--repo",type=Path,required=True)
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    raw=(args.repo/PARENT_REL).read_bytes()
    require(hashlib.sha256(raw).hexdigest()==PARENT_SHA256,"parent hash mismatch")
    p=build(json.loads(raw))
    receipt={"packet":p,"verification":check(p),"status":"PASS"}
    args.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"PASS","output":str(args.output),"ledger":p["ledger"],"witnesses":len(p["witnesses"]),"degree":p["exact_degree"]}))
    pp=reduce_auxiliary(p)
    rr={"packet":pp,"verification":check(pp),"status":"PASS"}
    other=args.output.with_name("fixed_blank_68.json")
    other.write_text(json.dumps(rr,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"PASS","output":str(other),"ledger":pp["ledger"],"witnesses":len(pp["witnesses"]),"degree":pp["exact_degree"]}))
    for base in (p,pp):
        system=comparison_system(base)
        integer=integer_lift(base)
        variants_check=check_variants(base,system,integer)
        system["verification"]=variants_check
        integer["verification"]=variants_check
        target=args.output.with_name(system["name"]+".json")
        target.write_text(json.dumps(system,indent=2,sort_keys=True)+"\n")
        print(json.dumps({"output":str(target),"ledger":system["ledger"],"equations":len(system["comparisons"]),"SOS":system["sum_of_squares"]["ledger"],"SOS_degree":system["sum_of_squares"]["exact_degree"]}))
        target=args.output.with_name(integer["name"]+".json")
        target.write_text(json.dumps(integer,indent=2,sort_keys=True)+"\n")
        print(json.dumps({"output":str(target),"integer_variables":len(integer["witnesses"]),"degree":integer["exact_degree"],"ledger":integer["ledger"]}))
        integer41=integer_lift(base,True)
        integer41["verification"]=check_variants(base,system,integer41)
        target=args.output.with_name(integer41["name"]+".json")
        target.write_text(json.dumps(integer41,indent=2,sort_keys=True)+"\n")
        print(json.dumps({"output":str(target),"integer_variables":len(integer41["witnesses"]),"degree":integer41["exact_degree"],"ledger":integer41["ledger"]}))

if __name__=="__main__": main()
