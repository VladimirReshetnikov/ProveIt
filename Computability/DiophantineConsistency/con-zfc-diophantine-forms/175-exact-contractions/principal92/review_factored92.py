"""Independent graph, degree-witness and coefficient-bound audit.

This uses simultaneous triangular definitions and a dependency topological
sort, rather than importing the producer or its sequential checker.
"""
import argparse
import hashlib
import json
from pathlib import Path


def require(ok,message):
    if not ok:raise ValueError(message)


def read_terms(ts,n):
    p={}
    for a,mon in ts:
        require(type(a)is int and a!=0,"invalid integer coefficient")
        require(type(mon)is list and all(type(v)is int and 0<=v<n for v in mon),"bad monomial")
        key=tuple(mon)
        require(key==tuple(sorted(key)) and key not in p,"uncollected monomial")
        p[key]=a
    return p


def dependencies(p):return {v for mon in p for v in mon}


def main():
    root=Path(__file__).resolve().parent.parent
    ap=argparse.ArgumentParser()
    ap.add_argument("--source",type=Path,default=root/"dag_search/source191.json")
    ap.add_argument("--certificate",type=Path,default=root/"dag_search/sextic191_cap512.json")
    ap.add_argument("--witness",type=Path,default=root/"dag_search/sextic191_cap512_check.json")
    ap.add_argument("--receipt",type=Path)
    args=ap.parse_args()
    raw=args.source.read_bytes();source=json.loads(raw)
    cert_raw=args.certificate.read_bytes();cert=json.loads(cert_raw)
    require(hashlib.sha256(raw).hexdigest()==cert["source_sha256"],"source pin differs")
    n=len(source["variables"])
    rows=[read_terms(row["terms"],n) for row in source["residuals"]]
    defs={};deleted=set()
    for step in cert["steps"]:
        v=step["variable"];r=step["row"];a=step["coefficient"]
        require(type(v)is int and 0<=v<n and v not in defs,"coordinate deletion")
        require(type(r)is int and 0<=r<len(rows) and r not in deleted,"row deletion")
        require(type(a)is int and a in (-1,1) and rows[r].get((v,))==a,"nonunit or incorrect pivot")
        other={m:b for m,b in rows[r].items() if m!=(v,)}
        require(v not in dependencies(other),"raw pivot is not monic linear")
        f=read_terms(step["restoration_source_terms"],n)
        require(f=={m:-a*b for m,b in other.items()},"incorrect integer restoration")
        defs[v]=f;deleted.add(r)
    free=[i for i in range(n) if i not in defs]
    retained=[i for i in range(len(rows)) if i not in deleted]
    require(free==cert["free_source_variables"],"free coordinates")
    require(retained==cert["retained_source_rows"],"retained rows")
    require(len(free)==cert["variables_remaining"] and len(retained)==cert["residuals_remaining"],"counts")
    pending={v:dependencies(f)&defs.keys() for v,f in defs.items()}
    order=[]
    while pending:
        available=sorted(v for v,needed in pending.items() if not needed)
        require(available,"cyclic simultaneous restorations")
        for v in available:order.append(v);del pending[v]
        for needed in pending.values():needed.difference_update(available)
    witness=json.loads(args.witness.read_text())["leading_witness"]
    modulus=witness["modulus"];ray=witness["free_coordinate_ray"]
    require(type(modulus)is int and modulus>1,"modulus")
    require(len(ray)==len(free) and all(type(x)is int for x in ray),"integer ray")
    degree={v:1 for v in free};leading=dict(zip(free,[x%modulus for x in ray]));norm={v:1 for v in free}
    def evaluate(p):
        d=max((sum(degree[v] for v in m) for m in p),default=0)
        lc=0;bound=0
        for m,a in p.items():
            term=abs(a);value=a
            for v in m:term*=norm[v];value=value*leading[v]%modulus
            bound+=term
            if sum(degree[v] for v in m)==d:lc=(lc+value)%modulus
        return d,lc,bound
    for v in order:degree[v],leading[v],norm[v]=evaluate(defs[v])
    evaluated={r:evaluate(rows[r]) for r in retained}
    upper=max(x[0] for x in evaluated.values())
    require(upper==cert["residual_degree_upper_bound"],"residual degree bound")
    r=witness["source_row"]
    require(r in retained and evaluated[r][0]==upper,"leading witness degree")
    require(evaluated[r][1]==witness["leading_coefficient_modulus"]!=0,"nonzero leading residue")
    require(cert["polynomial_degree_upper_bound"]==2*upper,"polynomial degree bound")
    live=set();todo=list({v for r in retained for v in dependencies(rows[r])})
    while todo:
        v=todo.pop()
        if v in live:continue
        live.add(v)
        if v in defs:todo.extend(dependencies(defs[v]))
    require(set(free)<=live,"unused free coordinate")
    require(set(defs)<=live,"unused restoration abbreviation")
    norm_bound=sum(x[2]*x[2] for x in evaluated.values())
    literal_height=max(abs(a) for p in list(defs.values())+[rows[r] for r in retained] for a in p.values())
    report={"status":"passed","source_sha256":hashlib.sha256(raw).hexdigest(),
            "certificate_sha256":hashlib.sha256(cert_raw).hexdigest(),
            "source_variables":n,"source_rows":len(rows),
            "integer_unit_definitions":len(defs),"live_definitions":len(set(defs)&live),
            "free_integer_coordinates":len(free),"live_free_coordinates":len(set(free)&live),
            "retained_residuals":len(retained),"topological_restoration_order":order,
            "exact_polynomial_degree":2*upper,"leading_witness":witness,
            "largest_literal_coefficient":literal_height,
            "expanded_coefficient_height_strict_power_of_two_bound":norm_bound.bit_length(),
            "l1_upper_bound":str(norm_bound),
            "max_residual_l1_upper_bound_bits":max(x[2].bit_length() for x in evaluated.values()),
            "expanded_coefficient_height_computed_exactly":False,
            "conclusion":"finite ordinary integer polynomial; unique integer restoration; exact degree witnessed without full expansion"}
    if args.receipt:args.receipt.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k not in {"topological_restoration_order","leading_witness","l1_upper_bound"}},indent=2,sort_keys=True))


if __name__=="__main__":main()
