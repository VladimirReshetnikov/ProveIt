#!/usr/bin/env python3
"""Independent finite checks of source216 reciprocal-pooling artifacts.

This file does not import the producer. Polynomial identities are checked
coefficient by coefficient. Circuit residuals are expanded independently;
the final sum of squares is checked in abstract residual variables, avoiding
expansion of the entire degree-22 polynomial. Unbounded arithmetic and the
source-to-ZFC calibration are separate proof obligations.
"""
from pathlib import Path
from collections import defaultdict
from functools import reduce
from random import Random
import copy
import hashlib
import json

ROOT = Path(__file__).resolve().parent
SOURCE_SHA256 = "e5e14bc0bbabb625f78ce57017fbdb336c4a65c5877f517142c399769992ff39"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def clean(p):
    return {m:c for m,c in p.items() if c}


def parse(terms):
    p = {}
    for c,m in terms:
        need(type(c) is int and c != 0, "invalid polynomial coefficient")
        need(all(type(v) is int and v >= 0 for v in m), "invalid variable index")
        need(m == sorted(m), "monomial indices must be sorted")
        m = tuple(m)
        need(m not in p, "duplicate sparse monomial")
        p[m] = c
    return p


def cst(c):
    return {():c} if c else {}


def var(v):
    return {(v,):1}


def add(*ps):
    d = defaultdict(int)
    for p in ps:
        for m,c in p.items():
            d[m] += c
    return clean(d)


def scale(k,p):
    return {m:k*c for m,c in p.items()} if k else {}


def mul(p,q):
    d = defaultdict(int)
    for m,c in p.items():
        for n,e in q.items():
            d[tuple(sorted(m+n))] += c*e
    return clean(d)


def prod(ps):
    return reduce(mul, ps, cst(1))


def square(p):
    return mul(p,p)


def same(p,q,label):
    need(p == q, label+": coefficient mismatch")


def remap(p,mapping):
    d = defaultdict(int)
    for m,c in p.items():
        need(all(i in mapping for i in m), "deleted private variable leaked")
        d[tuple(sorted(mapping[i] for i in m))] += c
    return clean(d)


def degree(p):
    return max(map(len,p), default=0)


def evaluate(p, point, modulus=None):
    total = 0
    for m,c in p.items():
        value = c
        for i in m:
            value *= point[i]
            if modulus:
                value %= modulus
        total += value
    return total % modulus if modulus else total


def block_data(a,base,requests):
    h,s,errors,yy,defects = {},{},{},{},{}
    for r in requests:
        m,x,y,z = (parse(r[k]) for k in ("m","X","Y","Z"))
        d = add(m,scale(-1,x),z)
        error = add(d,scale(-1,mul(base,y)))
        same(error,parse(r["error"]),"request error")
        same(add(x,scale(-1,z)),parse(r["D"]),"Pell difference offset")
        h = add(h,mul(y,add(m,scale(-1,x))))
        s = add(s,square(d),scale(-1,square(y)))
        errors = add(errors,square(error))
        yy = add(yy,square(y))
        defects = add(defects,mul(y,add(z,scale(-1,mul(a,y)))))
    t = add(scale(2,mul(a,base)),scale(-1,square(base)),cst(-1))
    e = add(s,scale(-2,mul(base,h)))
    same(add(e,scale(-1,mul(t,yy)),scale(-1,errors)),scale(2,mul(base,defects)),"pool identity modulo AY only")
    return {"H":h,"S":s,"E":e,"T":t,"base":base}


def verify_source(source,interface):
    need(len(source["variables"]) == 216 and len(source["residuals"]) == 153,"source size changed")
    rows = [parse(r["terms"]) for r in source["residuals"]]
    a = parse(interface["A"])
    req = {r["request"]:r for r in interface["requests"]}
    need(len(req) == 17,"request count")
    blocks = []
    removed_rows,removed_vars = [],[]
    covered = []
    for j,b in enumerate(interface["blocks"]):
        need(len(b["removed_rows"]) == len(b["removed_variables"]) == 2,"private block size")
        data = block_data(a,parse(b["base"]),[req[i] for i in b["requests"]])
        same(data["T"],parse(b["T"]),"source modulus")
        v,w = b["removed_variables"]
        if len(b["requests"]) == 1 and b["name"].startswith("singleton"):
            r = req[b["requests"][0]]
            expected = [add(var(v),scale(-1,data["T"])),add(parse(r["error"]),mul(var(v),var(w)))]
        else:
            expected = [add(var(v),scale(-2,data["H"]),scale(-1,mul(add(scale(2,a),scale(-1,data["base"])),var(w)))),add(data["S"],scale(-1,mul(data["base"],var(v))),var(w))]
        for q, row in zip(expected,b["removed_rows"]):
            need(row["sign"] in (-1,1),"invalid source row sign")
            same(q,scale(row["sign"],rows[row["row"]]),"private source row")
            removed_rows.append(row["row"])
        removed_vars += b["removed_variables"]
        covered += b["requests"]
        blocks.append(data)
    need(sorted(covered) == sorted(req) and len(covered) == len(set(covered)),"source request coverage")
    need(sorted(removed_rows) == interface["deleted_rows"],"deleted row ledger")
    need(sorted(removed_vars) == interface["deleted_variables"],"deleted coordinate ledger")
    retained_rows = sorted(set(range(153))-set(removed_rows))
    retained_vars = sorted(set(range(216))-set(removed_vars))
    need(retained_rows == interface["retained_rows"] and retained_vars == interface["retained_variables"],"retained ledger")
    for i in retained_rows:
        need(not (set(v for m in rows[i] for v in m)&set(removed_vars)),"private coordinate outside deleted rows")
    for p in interface["pairs"]:
        x,y,z = (parse(p[k]) for k in ("X","Y","Z"))
        same(add(z,scale(-1,mul(a,y))),scale(p["AY"]["sign"],rows[p["AY"]["row"]]),"retained AY identity")
        same(add(square(x),square(y),scale(-1,square(z)),cst(-1)),scale(p["norm"]["sign"],rows[p["norm"]["row"]]),"retained Pell norm")
        need(p["AY"]["row"] in retained_rows and p["norm"]["row"] in retained_rows,"deleted canonical pair row")
    atoms = [parse(t) for t in interface["frame"]["atoms"]]
    need(len(atoms) == 34,"square-frame atom count")
    w = add(scale(interface["frame"]["sign"],rows[interface["frame"]["row"]]),cst(2),*(square(p) for p in atoms))
    same(w,var(132),"literal W=2+sum of 34 squares")
    need(interface["frame"]["row"] in retained_rows and interface["orientation"]["row"] in retained_rows,"deleted frame or orientation")
    for r in req.values():
        for k in ("n","m","k"):
            need(parse(r[k]) in atoms,"request atom missing from square frame")
    same(rows[131],add(var(0),cst(-16),scale(-1,square(var(186)))),"t>=16 square row")
    need(131 in retained_rows,"deleted t bound")
    return rows,blocks


def expected_output(source,interface,eq,certificate):
    mode = eq.get("pooling_mode")
    need(mode == "unweighted","unexpected pooling mode")
    mapping = {int(k):v for k,v in eq["source_to_output"].items()}
    retained = interface["retained_variables"]
    need(mapping == {v:i for i,v in enumerate(retained)},"source coordinate map")
    need(eq["variables"][:len(retained)] == [{**source["variables"][i],"source_index":i} for i in retained],"retained variable names")
    need(len(eq["variables"]) == len(retained)+len(eq["pools"]),"new coordinate count")
    same(parse(eq["A"]),remap(parse(interface["A"]),mapping),"A remap")
    need(certificate["source_sha256"] == SOURCE_SHA256,"certificate source pin")
    for key in ("removed_rows","removed_variables","retained_rows","retained_variables"):
        expected = interface[{"removed_rows":"deleted_rows","removed_variables":"deleted_variables"}.get(key,key)]
        need(certificate[key] == expected,"certificate "+key)
    need(certificate["partition"] == [p["blocks"] for p in eq["pools"]],"partition certificate")
    source_requests = {r["request"]:r for r in interface["requests"]}
    out_requests = {r["request"]:r for r in eq["requests"]}
    need(set(source_requests)==set(out_requests),"output request coverage")
    for i,r in out_requests.items():
        for k in ("D","X","Y","Z","error","k","m","n"):
            same(parse(r[k]),remap(parse(source_requests[i][k]),mapping),"request remap "+k)
    need(len(eq["blocks"]) == 5,"missing block")
    block_polys = []
    for j,b in enumerate(eq["blocks"]):
        sb=interface["blocks"][j]
        need(b["name"]==sb["name"] and b["requests"]==sb["requests"],"block identity")
        same(parse(b["base"]),remap(parse(sb["base"]),mapping),"base remap")
        data=block_data(parse(eq["A"]),parse(b["base"]),[out_requests[i] for i in b["requests"]])
        for k,p in data.items():
            same(parse(b[k]),p,"emitted block "+k)
        block_polys.append(data)
    residuals=[]
    need(len(eq["quadratic_residuals"])==len(interface["retained_rows"]),"retained residual count")
    for row,j in zip(eq["quadratic_residuals"],interface["retained_rows"]):
        need(row["source_row"]==j,"retained source-row tag")
        p=remap(parse(source["residuals"][j]["terms"]),mapping)
        same(parse(row["terms"]),p,"literal retained row")
        need(degree(p)<=2,"nonquadratic retained row")
        residuals.append(p)
    covered=[]
    for i,pool in enumerate(eq["pools"]):
        ids=pool["blocks"]
        need(ids and len(set(ids))==len(ids) and all(0<=j<5 for j in ids),"pool block selection")
        need(pool["z"]==len(retained)+i,"new quotient index")
        covered+=ids
        ts=[block_polys[j]["T"] for j in ids]
        summands=[]
        for h,j in enumerate(ids):
            numer=block_polys[j]["E"]
            if mode=="oriented":
                numer=mul(numer,block_polys[j]["base"])
            summands.append(mul(numer,prod(ts[:h]+ts[h+1:])))
        residuals.append(add(*summands,scale(-1,mul(var(pool["z"]),prod(ts)))))
    need(sorted(covered)==list(range(5)),"pool partition must cover each block exactly once")
    return residuals


def circuit_values(circuit,point,modulus=None):
    values=[]
    for i,node in enumerate(circuit["nodes"]):
        op=node[0]
        if op=="var":
            need(len(node)==2 and 0<=node[1]<len(point),"invalid circuit variable")
            v=point[node[1]]
        elif op=="const":
            need(len(node)==2 and type(node[1]) is int,"invalid circuit integer")
            v=node[1]
        else:
            need(op in ("+","*","-") and len(node)==3 and all(type(j) is int and 0<=j<i for j in node[1:]),"non-topological circuit")
            l,r=(values[j] for j in node[1:])
            v=l+r if op=="+" else l*r if op=="*" else l-r
        values.append(v%modulus if modulus else v)
    return values


def circuit_gradient(circuit,point,p):
    values=circuit_values(circuit,point,p)
    adj=[0]*len(values)
    adj[circuit["output"]]=1
    gradient=[0]*len(point)
    for i in reversed(range(len(values))):
        node=circuit["nodes"][i]
        if node[0]=="var":
            gradient[node[1]]=(gradient[node[1]]+adj[i])%p
        elif node[0] in ("+","-","*"):
            l,r=node[1:]
            if node[0]=="*":
                adj[l]=(adj[l]+adj[i]*values[r])%p
                adj[r]=(adj[r]+adj[i]*values[l])%p
            else:
                adj[l]=(adj[l]+adj[i])%p
                adj[r]=(adj[r]+adj[i]*(1 if node[0]=="+" else -1))%p
    return gradient


def verify_circuit(circuit,expected,metrics):
    nodes=circuit["nodes"]
    outputs=circuit["residual_outputs"]
    need(len(outputs)==len(expected) and len(set(outputs))==len(outputs),"circuit residual outputs")
    need(all(type(i) is int and 0<=i<len(nodes) for i in outputs),"invalid residual pointer")
    need(type(circuit["output"]) is int and 0<=circuit["output"]<len(nodes),"invalid output pointer")
    circuit_values(circuit,[0]*len(circuit["variables"]))
    polynomial=[]
    for i,node in enumerate(nodes[:max(outputs)+1]):
        if node[0]=="var":
            q=var(node[1])
        elif node[0]=="const":
            q=cst(node[1])
        elif node[0]=="+":
            q=add(polynomial[node[1]],polynomial[node[2]])
        elif node[0]=="-":
            q=add(polynomial[node[1]],scale(-1,polynomial[node[2]]))
        else:
            q=mul(polynomial[node[1]],polynomial[node[2]])
        polynomial.append(q)
    for i,(wire,q) in enumerate(zip(outputs,expected)):
        same(polynomial[wire],q,"exact circuit residual "+str(i))
    # Check the final assembly with independent symbols for all already
    # computed wires. This proves that the output is the specified SOS.
    stop=max(outputs)+1
    abstract=[var(i) for i in range(stop)]
    for i,node in enumerate(nodes[stop:],stop):
        if node[0]=="const": q=cst(node[1])
        elif node[0]=="var": q=var(len(nodes)+node[1])
        elif node[0]=="+": q=add(abstract[node[1]],abstract[node[2]])
        elif node[0]=="-": q=add(abstract[node[1]],scale(-1,abstract[node[2]]))
        else: q=mul(abstract[node[1]],abstract[node[2]])
        abstract.append(q)
    same(abstract[circuit["output"]],add(*(square(var(i)) for i in outputs)),"abstract final SOS assembly")
    exact_degree=2*max(degree(q) for q in expected)
    need(metrics["exact_total_degree"]==exact_degree,"degree metadata")
    need(metrics["variables"]==len(circuit["variables"]),"variable metadata")
    need(metrics["residuals"]==len(expected),"residual metadata")
    need(set(v for q in expected for m in q for v in m)==set(range(len(circuit["variables"]))),"unused polynomial variable")
    degree_cert=metrics["degree_certificate"]
    point=[degree_cert["point"].get(str(i),0) for i in range(len(circuit["variables"]))]
    leading=[evaluate({m:c for m,c in q.items() if len(m)==degree(q)},point) for q in expected]
    need(leading==degree_cert["residual_leading_values"],"residual leading-degree witness")
    full_lead=sum(v*v for q,v in zip(expected,leading) if 2*degree(q)==exact_degree)
    need(full_lead==degree_cert["leading_value"] and full_lead>0,"nonzero degree witness")
    need([degree(q) for q in expected]==degree_cert["residual_degrees"],"residual degree list")
    reachable=set()
    todo=[circuit["output"]]
    while todo:
        i=todo.pop()
        if i in reachable: continue
        reachable.add(i)
        if nodes[i][0] in ("+","-","*"): todo.extend(nodes[i][1:])
    operations=sum(nodes[i][0] in ("+","-","*") for i in reachable)
    need(operations==metrics["binary_operations"],"live operation count")
    need(max(abs(nodes[i][1]) for i in reachable if nodes[i][0]=="const")==metrics["maximum_literal_integer"],"literal integer height")
    rng=Random(77117)
    for j in range(8):
        p=None if j<3 else 1000000007
        x=[rng.randint(-3,3) if p is None else rng.randrange(p) for _ in circuit["variables"]]
        values=circuit_values(circuit,x,p)
        rowvalues=[evaluate(q,x,p) for q in expected]
        need([values[i] for i in outputs]==rowvalues,"numeric residual replay")
        expected_value=sum(v*v for v in rowvalues)
        if p: expected_value%=p
        need(values[circuit["output"]]==expected_value,"numeric full polynomial replay")
    # Nonzero derivatives at one modular point certify actual dependence,
    # independently of syntactic support; failures trigger another point.
    p=1000000007
    live=set()
    for _ in range(3):
        point=[rng.randrange(p) for _ in circuit["variables"]]
        live.update(i for i,v in enumerate(circuit_gradient(circuit,point,p)) if v)
    need(live==set(range(len(circuit["variables"]))),"functional variable dependence")
    return {"variables":len(circuit["variables"]),"residuals":len(expected),"exact_degree":exact_degree,"live_binary_operations":operations,"expanded_residual_monomials":sum(map(len,expected)),"exact_circuit_residuals":len(expected),"numeric_replays":8,"all_variables_have_nonzero_derivative_certificate":True}


def reject_mutant(label,fn):
    try:
        fn()
    except (ValueError,KeyError,IndexError):
        return label
    raise ValueError("negative control accepted: "+label)


def main():
    source_path=ROOT/"inputs/source216.json"
    need(hashlib.sha256(source_path.read_bytes()).hexdigest()==SOURCE_SHA256,"source216 byte pin")
    source=json.loads(source_path.read_text())
    interface=json.loads((ROOT/"inputs/interface216.json").read_text())
    need(interface["source_sha256"]==SOURCE_SHA256,"interface source pin")
    verify_source(source,interface)
    results=[]
    snapshots={}
    for dirname in ("integer207_degree22","integer208_degree14","integer209_degree10","integer211_degree6"):
        d=ROOT/"equations"/dirname
        eq=json.loads((d/"equation.json").read_text())
        cert=json.loads((d/"certificate.json").read_text())
        circuit=json.loads((d/"circuit.json").read_text())
        metrics=json.loads((d/"METRICS.json").read_text())
        need(cert["result_sha256"]==hashlib.sha256((d/"equation.json").read_bytes()).hexdigest(),"result byte pin")
        need(eq["source_sha256"]==SOURCE_SHA256,"equation source pin")
        expected=expected_output(source,interface,eq,cert)
        need(circuit["variables"]==eq["variables"],"circuit/equation coordinates")
        result=verify_circuit(circuit,expected,metrics)
        results.append({"artifact":dirname,**result})
        snapshots[dirname]=(eq,cert,circuit,metrics,expected)
    eq,cert,circuit,metrics,expected=snapshots["integer207_degree22"]
    controls=[]
    bad=copy.deepcopy(eq); bad["blocks"][0]["E"][0][0]*=-1
    controls.append(reject_mutant("wrong numerator sign",lambda:expected_output(source,interface,bad,cert)))
    bad=copy.deepcopy(eq); bad["pools"][0]["blocks"].pop()
    bad_cert=copy.deepcopy(cert); bad_cert["partition"][0].pop()
    controls.append(reject_mutant("omitted block",lambda:expected_output(source,interface,bad,bad_cert)))
    bad_i=copy.deepcopy(interface); bad_i["frame"]["atoms"][-1]=copy.deepcopy(bad_i["frame"]["atoms"][-2])
    controls.append(reject_mutant("missing frame atom",lambda:verify_source(source,bad_i)))
    bad=copy.deepcopy(eq); bad["requests"][1]["Z"]=bad["requests"][1]["Z"][1:]
    controls.append(reject_mutant("lost affine offset",lambda:expected_output(source,interface,bad,cert)))
    bad_c=copy.deepcopy(circuit)
    first_binary=next(i for i,n in enumerate(bad_c["nodes"]) if n[0] in ("+","*","-"))
    bad_c["nodes"][first_binary][1]=first_binary
    controls.append(reject_mutant("circuit forward/self reference",lambda:circuit_values(bad_c,[0]*len(eq["variables"]))))
    return {"status":"pass","producer_imported":False,"source_sha256":SOURCE_SHA256,"source_frame_atoms":34,"source_requests":17,"source_blocks":5,"artifacts":results,"rejected_mutants":controls,"scope":"Exact finite source/circuit identities and arithmetic regressions. Unbounded pooling and source-to-ZFC calibration are proved separately."}


if __name__=="__main__":
    print(json.dumps(main(),indent=2))
