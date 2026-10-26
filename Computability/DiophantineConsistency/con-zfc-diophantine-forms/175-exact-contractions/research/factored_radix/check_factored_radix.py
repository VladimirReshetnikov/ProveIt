"""Independent literal/atom audit for the factored-radix semantic change.

No constructor or inherited executable module is imported. The mathematical
argument is in FACTORED_RADIX_PROOF.md; this program checks exact finite data.
"""
import argparse
from collections import Counter
from pathlib import Path
import copy
import hashlib
import json


def check(test, message):
    if not test:raise ValueError(message)


def clean(p):return {m:a for m,a in p.items() if a}
def plus(*args):
    r=Counter()
    for p in args:
        for m,a in p.items():r[m]+=a
    return clean(r)
def times(p,q):
    r=Counter()
    for m,a in p.items():
        for n,b in q.items():r[tuple(sorted(m+n))]+=a*b
    return clean(r)
def neg(p):return {m:-a for m,a in p.items()}
def number(a):return {():a} if a else {}
def coord(i):return {(i,):1}
def to_poly(terms):
    r=Counter()
    for a,m in terms:r[tuple(m)]+=a
    return clean(r)
def to_terms(p):return [[a,list(m)] for m,a in sorted(p.items())]
def replace(p,v,value):
    result={}
    for m,a in p.items():
        term=number(a)
        for i in m:term=times(term,value if i==v else coord(i))
        result=plus(result,term)
    return result


def audit(parent,equation):
    check(parent["domain"]=="unrestricted integers" and equation["domain"]=="Z","integer domains")
    check(len(parent["variables"])==225 and len(parent["residuals"])==162,"source dimensions")
    check(equation["schema"]==parent["schema"],"schema changed")
    check(equation["variant"]=="factored_radix224","unexpected endpoint variant")
    check(equation["polynomial"]=="sum of squares of all listed residuals","polynomial convention changed")
    oldnames={v["name"]:i for i,v in enumerate(parent["variables"])}
    V=lambda name:coord(oldnames[name])
    shifted=lambda name,k:plus(V(name),number(k))
    t=V("t0");fsq=V("mul.1");qold=shifted("pow2.output",-1)
    oldatoms=[("t",t),("t+1",plus(t,number(1))),
              ("F^2+t",plus(fsq,t)),("x",V("x")),
              ("F^2+1",plus(fsq,number(1))),
              ("B",V("choose0.output")),("V",V("pow0.output")),
              ("y+1=V",V("pow0.output")),("a",shifted("crt.encoded.a",-1))]
    for name in ["b","c","d","S","Sp","u","vq"]:
        oldatoms.append((name,V("crt.encoded."+name)))
    oldatoms.extend([("C",V("crt.encoded_index_minus_one")),("N",V("pow1.output")),
                     ("h",V("add.380")),("q",qold),
                     ("q+1",V("pow2.output")),("BH",V("self_radix.BH"))])
    request_ids=[3,4,5,7,8,9,10,11,12,13,14,15,16,17]
    for i in request_ids:oldatoms.append(("pow"+str(i)+".output",V("pow"+str(i)+".output")))
    old_frame=plus(V("shared.W"),number(-2),*(neg(times(a,a)) for label,a in oldatoms))
    oldframes=[(i,r) for i,r in enumerate(parent["residuals"]) if r["label"]=="shared.frame_definition"]
    check(len(oldframes)==1,"source frame count")
    frame_i,frame=oldframes[0]
    check(old_frame==to_poly(frame["terms"]),"source actual-atom identity")
    check(len(oldatoms)==36,"source atom count")
    N=V("pow1.output");P=V("pow2.output")
    representatives=[a for label,a in oldatoms if label in {"a","b","c","d","S","Sp","u","vq","C"}]
    H=plus(number(1),*(times(number(2),a) for a in representatives))
    check(len(representatives)==9,"majorant representative count")
    atoms=[(label,a) for label,a in oldatoms if label not in {"q","q+1","BH"}]
    atoms.extend([("P",P),("H",H)])
    check(len(atoms)==35,"new atom count")
    new_frame=plus(V("shared.W"),number(-2),*(neg(times(a,a)) for label,a in atoms))
    q=times(N,P);qplus=plus(q,number(1))
    requests={0:(plus(fsq,number(1)),t,V("pow0.output")),
              1:(V("choose0.output"),V("x"),N),
              2:(H,V("x"),P),
              3:(qplus,plus(fsq,t),V("pow3.output")),
              4:(q,t,V("pow4.output")),
              5:(qplus,shifted("crt.encoded.a",-1),V("pow5.output")),
              7:(qplus,V("crt.encoded.b"),V("pow7.output")),
              8:(qplus,V("crt.encoded.c"),V("pow8.output")),
              9:(qplus,V("crt.encoded.d"),V("pow9.output")),
              10:(qplus,V("crt.encoded.S"),V("pow10.output")),
              11:(q,V("pow0.output"),V("pow11.output")),
              12:(qplus,V("crt.encoded.Sp"),V("pow12.output")),
              13:(qplus,V("crt.encoded.u"),V("pow13.output")),
              14:(q,V("x"),V("pow14.output")),
              15:(qplus,V("crt.encoded.vq"),V("pow15.output")),
              16:(qplus,V("crt.encoded_index_minus_one"),V("pow16.output")),
              17:(qplus,V("add.380"),V("pow17.output"))}
    atom_values=[a for label,a in atoms]
    wide_requests=[]
    for i,(base,index,output) in requests.items():
        check(index in atom_values,"unbounded intended index "+str(i))
        check(output in atom_values,"unbounded intended output "+str(i))
        if base not in atom_values:
            check(base in [q,qplus],"unbounded intended base "+str(i))
            wide_requests.append(i)
    A=shifted("shared.A",1);B=V("choose0.output");BH=V("self_radix.BH")
    T=V("base2.T");Q=V("pow2.quotient");Y=V("index12.Y");D=V("index12.X_minus_AY")
    old_def=plus(BH,neg(times(B,H)))
    old_mod=plus(times(number(2),times(A,BH)),neg(times(BH,BH)),number(-1),neg(T))
    old_pow=plus(qold,times(T,Q),neg(D),neg(times(BH,Y)))
    pos=lambda value:[i for i,r in enumerate(parent["residuals"]) if to_poly(r["terms"])==value]
    dpos,mpos,ppos=pos(old_def),pos(old_mod),pos(old_pow)
    check(len(dpos)==len(mpos)==len(ppos)==1,"source changed-row identities")
    new_mod=plus(times(number(2),times(A,H)),neg(times(H,H)),number(-1),neg(T))
    new_pow=plus(P,times(T,Q),neg(D),neg(times(H,Y)))
    special={frame_i:new_frame,mpos[0]:new_mod,ppos[0]:new_pow}
    deleted=oldnames["self_radix.BH"];qindex=oldnames["pow2.output"]
    expected=[];expected_labels=[]
    changed_labels={frame_i:"factored_radix.semantic_frame",mpos[0]:"factored_radix.H_modulus",
                    ppos[0]:"factored_radix.H_power"}
    for i,r in enumerate(parent["residuals"]):
        if i==dpos[0]:continue
        row=special[i] if i in special else replace(to_poly(r["terms"]),qindex,qplus)
        check(not any(deleted in m for m in row),"BH coordinate survives")
        row={tuple(v-(v>deleted) for v in m):a for m,a in row.items()}
        expected.append(row)
        expected_labels.append(changed_labels.get(i,r["label"]))
    actual=[to_poly(r["terms"]) for r in equation["residuals"]]
    check(expected==actual,"literal changed residuals differ")
    check(expected_labels==[r["label"] for r in equation["residuals"]],"residual labels differ")
    check(len(equation["variables"])==224 and len(actual)==161,"changed dimensions")
    expected_variables=[dict(v) for i,v in enumerate(parent["variables"]) if i!=deleted]
    expected_variables[qindex-(qindex>deleted)]={"kind":"witness","name":"self_radix.powerH"}
    check(equation["variables"]==expected_variables,"full variable metadata differ")
    check(max(len(m) for r in actual for m in r)==3,"source exact residual degree")
    expanded=plus(*(times(r,r) for r in actual))
    check(max(map(len,expanded))==6,"source polynomial degree")
    return {"status":"passed","source_atoms":len(oldatoms),"new_atoms":len(atoms),
            "requests":len(requests),"requests_with_wider_base_bound":wide_requests,
            "all_index_and_output_squares_below_W":True,
            "q_and_q_plus_one_bounds":"abs(NP)<= (N^2+P^2)/2 <=(W-2)/2; abs(NP+1)<=W/2",
            "canonical_index_list_unchanged":True,
            "literal_rows_checked":len(actual),"variables":224,"degree":6,
            "variable_metadata_and_row_labels_checked":True,
            "terms":len(expanded),"height":max(map(abs,expanded.values())),
            "private_Pell_variables_in_frame":False,
            "frame_ledger":[{"name":label,"terms_in_parent_coordinates":to_terms(a)} for label,a in atoms],
            "power_requests":[{"source_request":i,"base":to_terms(base),"index":to_terms(index),"output":to_terms(output)}
                              for i,(base,index,output) in requests.items()]}


def main():
    here=Path(__file__).resolve().parent
    root=here.parent.parent
    parser=argparse.ArgumentParser()
    parser.add_argument("--parent",type=Path,default=root/"sources/p225.json")
    parser.add_argument("--equation",type=Path,default=here/"factored_radix224/equation.json")
    parser.add_argument("--receipt",type=Path)
    args=parser.parse_args();praw=args.parent.read_bytes();raw=args.equation.read_bytes()
    parent=json.loads(praw);equation=json.loads(raw)
    check(equation["source_equation_sha256"]==hashlib.sha256(praw).hexdigest(),"source digest mismatch")
    receipt=audit(parent,equation)
    corrupted=copy.deepcopy(equation);corrupted["residuals"][0]["terms"][0][0]+=1
    rejected=False
    try:audit(parent,corrupted)
    except ValueError:rejected=True
    check(rejected,"corruption control accepted")
    receipt["corruption_control_rejected"]=True
    receipt["parent_sha256"]=hashlib.sha256(praw).hexdigest()
    receipt["equation_sha256"]=hashlib.sha256(raw).hexdigest()
    if args.receipt:args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:v for k,v in receipt.items() if k not in {"frame_ledger","power_requests"}},indent=2,sort_keys=True))


if __name__=="__main__":main()
