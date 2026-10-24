#!/usr/bin/env python3
"""Produce exact original-row certificates for five presemantic signs."""
import argparse
from collections import Counter
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'candidates/projected-radius-mixed-bounds'


def need(ok,text):
    if not ok:raise ValueError(text)


def encoded(v):return (json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()
def load(path):return json.loads(path.read_text())


def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(sha256((ROOT/n).read_bytes()).hexdigest()==h,'frozen input '+n)
    spec=importlib.util.spec_from_file_location('frozen_polynomial_arithmetic',ROOT/'candidates/retained-radius-bounds/check.py')
    b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
    raw=load(BASE/'source/raw_builder.json');body=load(BASE/'source/natural667.json')
    parent=load(BASE/'domain_certificate.json');old=load(ROOT/'candidates/projected-radius-mixed-retained/source/old_raw_domain.json')['positivity']
    definitions={r['gate']:i for i,r in enumerate(raw['rows'])if r.get('gate')is not None}
    def atom(v):return{(v,):1}
    one={():1}
    def plus(*ps):
        out={}
        for p in ps:out=b.add(out,p)
        return out
    def times(*ps):
        out=one
        for p in ps:out=b.mul(out,p)
        return out
    def scalar(c):return{():c}if c else{}
    def cut(row,leaves):
        p=b.poly(raw['rows'][row]['terms']);combination={row:one}
        while True:
            options=[v for m in p for v in m if v not in leaves and v in definitions]
            if not options:break
            v=max(options);mon=next(m for m in p if v in m);c=p[mon]
            residual=list(mon);residual.remove(v);multiple={tuple(residual):c};rid=definitions[v]
            defining=b.poly(raw['rows'][rid]['terms'])
            need(defining.get((v,))==1 and all(v not in m or m==(v,)for m in defining),'monic local raw gate')
            p=b.add(p,b.mul(multiple,defining),-1)
            combination[rid]=b.add(combination.get(rid,{}),multiple,-1)
        return p,{i:q for i,q in combination.items()if q}
    def combine(parts):
        result={}
        for comb,mult in parts:
            for row,p in comb.items():result[row]=b.add(result.get(row,{}),b.mul(p,mult))
        return [dict(row=i,multiplier=[[c,list(m)]for m,c in sorted(p.items())])for i,p in sorted(result.items())if p]
    specs=[]
    for target,C,V,r,s,erow,hrow in [(87,91,93,94,95,82,85),(107,111,113,114,115,97,100)]:
        E,e=cut(erow,{target,C,V,r,s});H,h=cut(hrow,{target,C,V,r,s})
        need(E==plus(atom(C),atom(V),times(scalar(-1),atom(target),atom(C)),times(scalar(-1),atom(r)),scalar(-1)),'actual factorial ceiling')
        need(H==plus(atom(C),times(scalar(-1),atom(r)),times(scalar(-1),atom(s)),scalar(-1)),'actual factorial remainder bound')
        specs.append(dict(variable=target,lower=0,factor=plus(atom(r),atom(s),one),rhs=plus(atom(V),atom(s)),
            row_combination=combine([(e,scalar(-1)),(h,plus(one,times(scalar(-1),atom(target))))]),
            role='factorial output from positive ceiling divisor'))
    a,c,f,q,R,d,s,i=123,106,107,130,129,126,131,59
    E,e=cut(109,{a,c,f,q,R,d});H,h=cut(112,{d,R,s});K,k=cut(117,{R,87,i})
    N=times(atom(a),atom(c),atom(f));M=plus(one,times(atom(87),plus(one,atom(i))))
    need(E==plus(N,times(scalar(-1),atom(R)),times(scalar(-1),atom(d),atom(q))),'actual product division')
    need(H==plus(atom(d),times(scalar(-1),atom(R)),times(scalar(-1),atom(s)),scalar(-1)),'actual product remainder bound')
    need(K==b.add(M,atom(R),-1),'actual canonical product remainder')
    specs.append(dict(variable=q,lower=0,factor=plus(M,atom(s),one),rhs=b.add(N,M,-1),
        row_combination=combine([(e,scalar(-1)),(h,times(scalar(-1),atom(q))),
            (k,plus(atom(q),one))]),role='moduli-product quotient from two-sided remainder bound'))
    q=517
    E,e=cut(496,{516,129,q})
    need(E==plus(atom(516),times(scalar(-1),atom(129),atom(q))),'actual nonnegative evaluation division')
    specs.append(dict(variable=q,lower=0,factor=M,rhs=atom(516),
        row_combination=combine([(e,scalar(-1)),(k,atom(q))]),
        role='evaluation quotient from positive canonical modulus and sign-certified numerator'))
    q,u,m,r,n,y,x=32,30,3,31,5,2,1
    E,e=cut(32,{x,m,u,y});L,l=cut(38,{x,q,y,n});H,h=cut(35,{y,m,r})
    Y=plus(atom(m),atom(r),scalar(2))
    need(E==plus(atom(x),times(scalar(-1),atom(m)),scalar(-2),times(scalar(-1),atom(u),plus(atom(y),one))),'actual first endpoint quotient')
    need(L==plus(atom(x),scalar(-1),times(scalar(-1),atom(q),plus(times(atom(y),atom(n)),one))),'actual last endpoint quotient')
    need(H==b.add(atom(y),Y,-1),'actual endpoint remainder')
    specs.append(dict(variable=q,lower=1,factor=plus(times(Y,atom(n)),one),
        rhs=plus(atom(m),one,times(atom(u),plus(Y,one))),
        row_combination=combine([(e,one),(l,scalar(-1)),
            (h,plus(atom(u),times(scalar(-1),atom(q),atom(n))))]),
        role='last endpoint quotient from retained first quotient and endpoint remainder'))
    removed={s['variable']for s in specs}
    old_seeds=[g['raw_variable']for g in parent['guards']]
    seeds=set(old_seeds)-removed
    need(len(seeds)==102 and len(removed)==5 and removed<=set(old_seeds),'five actual formerly guarded raw values')
    known=seeds|{s['variable']for s in parent['bound_steps']}
    inferences=list(old['proof_steps'])
    present={(s['variable'],s['row'])for s in inferences}
    # The old greedy ledger sometimes selected an equality with a quotient
    # rather than an available monotone defining row. Add all such literal
    # forward rows so the fresh proof need not inherit that dependency.
    for rid,row in enumerate(raw['rows']):
        v=row.get('gate')
        if v is None or (v,rid)in present:continue
        p=b.poly(row['terms'])
        if p.get((v,))!=1 or any(v in m and m!=(v,)for m in p):continue
        rhs={m:-c for m,c in p.items()if m!=(v,)}
        if not all(c>0 for c in rhs.values()):continue
        dependencies={i for m in rhs for i,k in Counter(m).items()if k%2}
        inferences.append(dict(variable=v,row=rid,coefficient=1,kind='positive_monomials',
            rhs=[[c,list(m)]for m,c in sorted(rhs.items())],dependencies=sorted(dependencies),
            name=raw['variables'][v]['name']))
    for stage in specs:
        trace=[]
        while True:
            changed=False
            for step in inferences:
                dependencies=set()if step['kind']=='affine_square'else{
                    v for c,m in step['rhs']for v,k in Counter(m).items()if k%2}
                if step['variable']not in known and dependencies<=known:
                    known.add(step['variable']);trace.append(step);changed=True
            if not changed:break
        need(stage['variable']not in known,'new sign not assumed or inferred cyclically')
        stage['preceding_sign_steps']=trace
        for field in ['factor','rhs']:stage[field]=[[c,list(m)]for m,c in sorted(stage[field].items())]
        known.add(stage['variable']);stage['known_after']=sorted(known)
    need(set(old_seeds)<=known,'all old107 signs recovered')
    reverse={g['raw_variable']:g['variable']for g in parent['guards']}
    certificate=dict(schema='five_original_row_sign_consequences_v1',
        remaining_raw_guard_indices=sorted(seeds),removed_guard_identities=[dict(raw_variable=v,
            contracted_variable=reverse[v],metadata=raw['variables'][v])for v in sorted(removed)],
        initial_bound_steps=parent['bound_steps'],stages=specs,
        all_original_guard_indices=old_seeds,known_after=sorted(known),
        conclusion='Every zero with102 retained guards satisfies all107 old guards; fresh15 Legendre witnesses extend it to literal988. No power or Pell interpretation is used.')
    return encoded(certificate)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    data=generate();path=HERE/'CERTIFICATE.json'
    if args.check:need(path.read_bytes()==data,'entire deterministic sign certificate')
    else:path.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,certificate_sha256=sha256(data).hexdigest()),indent=2))


if __name__=='__main__':main()
