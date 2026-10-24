#!/usr/bin/env python3
"""Audit product-strengthened common Pell-index certificates."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import gcd,prod
from pathlib import Path

from build_equation import const
from shared_product_power import SharedProductPowerBuilder
from audit_shared_power import P,require,symbolic_rows,pell,evaluate


def exact_audit():
    b=SharedProductPowerBuilder()
    n0,n1,k0,k1=[b.new(s) for s in("n0","n1","k0","k1")]
    calls=[(n0,k0),(n1,k0),(n0,k1)]
    outputs=[b.power(n,k) for n,k in calls]
    b.finalize_power_frame()
    values,actual=symbolic_rows(b)
    names={v["name"]:values[i] for i,v in enumerate(b.variables)}
    at=lambda a:P.coerce(a[1]) if a[0]=="c" else values[a[1]]
    W,A,Z=names["shared.W"],names["shared.A"],names["shared.Zminus1"]+1
    U,V=names["shared_index.U"],names["shared_index.V"]
    B=1+4*V*(names["shared_index.q4minus1"]+1)
    norm=lambda a,x,y:x*x-1-(a*a-1)*y*y
    expected=[("shared.last_norm",(A*A-1-W**3*(W+2)*Z*Z).key()),
              ("shared_index.norm",norm(A,U,V).key()),
              ("shared_index.B_mod_U",(B-A-U*names["shared_index.Bquotient"]).key())]
    atoms={a for(n,k),m in zip(calls,outputs) for a in(n,k,m)}
    expected.append(("shared.frame_definition",(W-2-sum((at(a) for a in atoms),P())).key()))
    Yprod=P.coerce(1)
    for j,k in enumerate((k0,k1)):
        pre="index"+str(j)+"."
        X,Y,S,R=[names[pre+s] for s in("X","Y","S","R")]
        Yprod*=Y*Y
        ps={"index_at_most_Y":Y-at(k)-names[pre+"YminusK"],
            "norm1":norm(A,X,Y),"norm3":norm(B,S,R),
            "S_mod_U":S-X-U*names[pre+"Squotient"],
            "R_mod_4Y":R-at(k)-4*Y*names[pre+"Rquotient"]}
        expected.extend((pre+s,p.key()) for s,p in ps.items())
    expected.append(("shared_index.V_positive_product",
                     (V-Yprod*(names["shared_index.Vquotient_minus1"]+1)).key()))
    for j,n in enumerate((n0,n1)):
        T=names["base"+str(j)+".T"]
        expected.append(("base"+str(j)+".T_definition",(2*A*at(n)-T-at(n)**2-1).key()))
    for j,((n,k),m) in enumerate(zip(calls,outputs)):
        ij=0 if k==k0 else 1
        bj=0 if n==n0 else 1
        X,Y=[names["index"+str(ij)+"."+s] for s in("X","Y")]
        T=names["base"+str(bj)+".T"]
        pol=X+Y*at(n)-A*Y-at(m)-T*names["pow"+str(j)+".quotient"]
        expected.append(("pow"+str(j)+".power_congruence",pol.key()))
    require(actual==Counter(expected),"product-index constraints differ from mathematical system")
    return {"exact_scalar_constraints":len(expected),"definitional_gates":len(b.gates),
            "exponent_families":2,"common_U_V_B_triples":1,
            "global_V_divisibility_products":1,"global_B_mod_4V_constraints":1}


def family(A,exponents):
    coords=[pell(A,k) for k in exponents]
    K=prod(Y*Y for X,Y in coords)
    L=4*K
    x,y=1,0
    d=A*A-1
    r=None
    for j in range(1,L*L+1):
        x,y=(A*x+d*y)%L,(x+A*y)%L
        if(x,y)==(1,0):
            r=j
            break
    require(r is not None,"finite unit order not found")
    U,V=pell(A,r)
    require(U%L==1 and V%L==0 and V>0,"common auxiliary Pell congruences")
    require(gcd(U,4*V)==1,"strengthened CRT coprimality")
    B=A+U*(((1-A)*pow(U,-1,4*V))%(4*V))
    if B<=A:
        B+=4*U*V
    result=[]
    for k,(X,Y) in zip(exponents,coords):
        S,R=pell(B,k)
        require(B>A and S>=X and R>=k,"common quotient signs")
        require((B-1)%(4*Y)==0 and (S-X)%U==0 and (R-k)%(4*Y)==0,
                "restored index congruence")
        result.append(dict(X=X,Y=Y,S=S,R=R,YminusK=Y-k,
                           Squotient=(S-X)//U,Rquotient=(R-k)//(4*Y)))
    global_values=dict(U=U,V=V,q4minus1=(B-1)//(4*V)-1,
                       Bquotient=(B-A)//U,Vquotient_minus1=V//K-1)
    return global_values,B,result,r


def finite_audit():
    cases=mutations=0
    for bases in((1,),(1,2),(1,2,3)):
        b=SharedProductPowerBuilder()
        for n in bases:
            b.power(const(n),const(1))
        b.finalize_power_frame()
        W=2+sum(set(bases)|{1})+sum(bases)
        A,Yframe=pell(W+1,W)
        global_values,B,indices,order=family(A,[1])
        assignment={"shared.W":W,"shared.A":A,"shared.Zminus1":Yframe//W-1}
        assignment.update({"shared_index."+k:v for k,v in global_values.items()})
        assignment.update({"index0."+k:v for k,v in indices[0].items()})
        for j,n in enumerate(bases):
            T=2*A*n-n*n-1
            h=(indices[0]["X"]-(A-n)*indices[0]["Y"]-n)//T
            assignment.update({"base"+str(j)+".T":T,"pow"+str(j)+".output":n,
                               "pow"+str(j)+".quotient":h})
        require(not any(evaluate(b,assignment)[1]),"complete product-index graph fixture")
        for j,n in enumerate(bases):
            changed=dict(assignment)
            changed["pow"+str(j)+".output"]=n+1
            require(any(evaluate(b,changed)[1]),"changed output escaped product graph")
            mutations+=1
        cases+=1
    periods=[]
    for A in(2,3,4):
        glob,B,indices,r=family(A,[1,2])
        U,V=glob["U"],glob["V"]
        require(U*U-(A*A-1)*V*V==1,"auxiliary Pell norm")
        require((B-1)%(4*V)==0,"global modulus 4V")
        K=prod(z["Y"]**2 for z in indices)
        require(V%K==0 and V//K>=1,"global divisor product")
        for z in indices:
            require(z["X"]**2-(A*A-1)*z["Y"]**2==1,"main index norm")
            require(z["S"]**2-(B*B-1)*z["R"]**2==1,"common base norm")
        periods.append({"A":A,"exponents":[1,2],"finite_unit_period":r})
    return {"complete_graph_fixtures":cases,"changed_outputs_rejected":mutations,
            "simultaneous_nontrivial_index_fixtures":periods}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args()
    here=Path(__file__).resolve().parent
    result={"status":"PASS","exact_structure":exact_audit(),"finite_controls":finite_audit(),
            "optimized_python":not __debug__,
            "scope":"Exact graph identities and finite controls of product-strengthened Pell index graphs; universal proof in shared_index_proof.md.",
            "sha256":{n:sha256((here/n).read_bytes()).hexdigest() for n in
                      ("shared_product_power.py","shared_power.py","audit_shared_product.py","audit_shared_power.py")}}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=="__main__":
    main()
