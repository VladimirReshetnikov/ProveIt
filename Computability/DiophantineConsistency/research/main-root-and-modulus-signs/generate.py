#!/usr/bin/env python3
"""Exact core-positive, frame, seed and chosen-call data for21 guard signs."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'candidates/projected-radius-mixed-bounds'


def need(ok,text):
    if not ok:raise ValueError(text)


def load(p):return json.loads(p.read_text())
def enc(v):return(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode()


def generate():
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(sha256((ROOT/n).read_bytes()).hexdigest()==h,'frozen input '+n)
    spec=importlib.util.spec_from_file_location('frozen_sparse_polynomial_operations',ROOT/'candidates/retained-radius-bounds/check.py')
    b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
    raw=load(BASE/'source/raw_builder.json');old=load(ROOT/'candidates/projected-radius-mixed-orbits/domain_certificate.json')
    interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json')
    five=load(ROOT/'research/guard-seed-consequences/CERTIFICATE.json')
    definitions={r['gate']:i for i,r in enumerate(raw['rows'])if r.get('gate')is not None}
    one={():1}
    def atom(i):return{(i,):1}
    def plus(*ps):
        p={}
        for q in ps:p=b.add(p,q)
        return p
    def times(*ps):
        p=one
        for q in ps:p=b.mul(p,q)
        return p
    def scalar(c):return{():c}if c else{}
    def cut(row,leaves):
        p=b.poly(raw['rows'][row]['terms']);comb={row:one}
        while True:
            options=[v for m in p for v in m if v not in leaves and v in definitions]
            if not options:break
            v=max(options);m=next(m for m in p if v in m);c=p[m];rest=list(m);rest.remove(v)
            multiplier={tuple(rest):c};rid=definitions[v];r=b.poly(raw['rows'][rid]['terms'])
            need(r.get((v,))==1 and all(v not in m or m==(v,)for m in r),'literal monic cut gate')
            p=b.add(p,b.mul(multiplier,r),-1);comb[rid]=b.add(comb.get(rid,{}),multiplier,-1)
        return dict(polynomial=[[c,list(m)]for m,c in sorted(p.items())],
            row_combination=[dict(row=i,multiplier=[[c,list(m)]for m,c in sorted(q.items())])for i,q in sorted(comb.items())if q])
    def step_for(rid):
        row=raw['rows'][rid];v=row['gate'];p=b.poly(row['terms'])
        need(p.get((v,))==1,'literal forward gate pivot')
        rhs={m:-c for m,c in p.items()if m!=(v,)}
        need(all(c>0 for c in rhs.values()),'literal monotone gate')
        dependencies={i for m in rhs for i,k in Counter(m).items()if k%2}
        return dict(variable=v,row=rid,coefficient=1,kind='positive_monomials',name=raw['variables'][v]['name'],
            rhs=[[c,list(m)]for m,c in sorted(rhs.items())],dependencies=sorted(dependencies))
    prefix_stages=[]
    for stage in five['stages']:
        s=deepcopy(stage);s.pop('known_after');s['preceding_sign_steps']=[x for x in s['preceding_sign_steps']if x['variable']<643]
        prefix_stages.append(s)
    canonical=cut(117,{129,87,59})
    M=plus(one,times(atom(87),plus(one,atom(59))))
    need(b.poly(canonical['polynomial'])==b.add(M,atom(129),-1),'literal positive canonical modulus')
    positive={4,5,129};positive_steps=[]
    while True:
        changed=False
        for rid,row in enumerate(raw['rows']):
            v=row.get('gate')
            if rid>=594 or v is None or v>=643 or v in positive:continue
            p=b.poly(row['terms'])
            if p.get((v,))!=1 or any(v in m and m!=(v,)for m in p):continue
            rhs={m:-c for m,c in p.items()if m!=(v,)}
            if not all(c>0 for c in rhs.values()):continue
            witnesses=[m for m in rhs if set(m)<=positive]
            if witnesses:
                positive_steps.append(dict(variable=v,row=rid,positive_monomial=list(min(witnesses))))
                positive.add(v);changed=True
        if not changed:break
    seed_k=[s['exponent'][1]for s in raw['seeds']]
    need(set(seed_k)<positive,'every actual seed exponent strictly positive')
    nonf0_bases=[5,92,103,112,531,530]
    need(set(nonf0_bases)<=positive,'all independent constructor bases strictly positive')
    args=sorted({x[1]for p in raw['powers']for x in[p['base'],p['exponent'],p['output']]})
    need(all(i<643 for i in args),'every actual power argument is in the independent prefix')
    frame=cut(1176,{643}|set(args));frame_expected=plus(atom(643),scalar(-2),*[{(i,):-1}for i in args])
    need(b.poly(frame['polynomial'])==frame_expected,'exact2+sum-distinct source frame')
    Tdata=[(5,694,644),(92,730,677),(103,742,689),(87,753,700),
           (112,764,711),(531,798,743),(530,810,755)]
    moduli=[]
    for n,T,rid in Tdata:
        c=cut(rid,{644,n,T})
        expected=plus(times(scalar(2),atom(644),atom(n)),times(scalar(-1),atom(T)),times(scalar(-1),atom(n),atom(n)),scalar(-1))
        need(b.poly(c['polynomial'])==expected,'literal source modulus')
        moduli.append(dict(base=n,modulus=T,row=rid,cut=c,early_positive_base=n!=87,
            retained_guard=T==694))
    by_base={x['base']:x for x in moduli}
    pairs={tuple(x['exponent']):x['pair']for x in raw['indices']}
    powers=[]
    for j,(p,inter)in enumerate(zip(raw['powers'],interfaces['powers'])):
        need(all(p[k]==inter[k]for k in['base','exponent','output']),'actual full call binding')
        n,k,m=[p[name][1]for name in['base','exponent','output']];X,Y=[x[1]for x in pairs[tuple(p['exponent'])]]
        h=inter['quotient'][1];T=by_base[n]['modulus'];c=cut(inter['row'],{644,n,m,X,Y,h,T})
        expected=plus(atom(X),times(atom(n),atom(Y)),times(scalar(-1),atom(644),atom(Y)),
            times(scalar(-1),atom(m)),times(scalar(-1),atom(T),atom(h)))
        need(b.poly(c['polynomial'])==expected,'literal power residue with its actual main pair')
        powers.append(dict(index=j,base=n,exponent=k,output=m,X=X,Y=Y,quotient=h,
            modulus=T,row=inter['row'],cut=c,semantic_value_used_before_all_guard_recovery=j==1))
    seeds=[]
    for s,inter in zip(raw['seeds'],interfaces['seeds']):
        need(s['exponent']==inter['exponent']and s['pair']==[inter['X'],inter['Y']],'all seed interfaces bound')
        X,Y,S,R,k,slack,sq,rq=[inter[key][1]for key in['X','Y','S','R','exponent','YminusK','Squotient','Rquotient']]
        selected=next(p['index']for p in powers if p['exponent']==k)
        need(powers[selected]['X']==X and powers[selected]['Y']==Y and powers[selected]['base']!=87,'an independent real call for every seed')
        aliases=dict(X=X,Y=Y,S=S,R=R,k=k,YminusK=slack,Squotient=sq,Rquotient=rq)
        leaves={644,667,655}|set(aliases.values())
        cuts={name:cut(rid,leaves)for name,rid in inter['rows'].items()}
        seeds.append(dict(aliases=aliases,rows=inter['rows'],cuts=cuts,selected_power_call=selected,
            exponent_strictly_positive=k in positive))
    unit=cut(609,{644,655,656});Bconstructor=cut(613,{667,656,657});Bcongruence=cut(616,{667,644,655,658})
    Ys={s['pair'][1][1]for s in raw['seeds']};Vproduct=cut(1133,{656,1214}|Ys)
    bootstrap=load(ROOT/'research/guard-sign-orbits/CERTIFICATE.json')['bootstrap_norm']
    removed={s['pair'][0][1]for s in raw['seeds']}|{T for n,T,rid in Tdata if T!=694}
    previous=[g['raw_variable']for g in old['guards']]
    need(len(removed)==21 and removed<=set(previous),'exact21 existing guarded values')
    identities={json.dumps(v,sort_keys=True,separators=(',',':')):i for i,v in enumerate(raw['variables'])}
    body=load(BASE/'source/natural667.json');reverse={identities[json.dumps(v,sort_keys=True,separators=(',',':'))]:i for i,v in enumerate(body['variables'])}
    cert=dict(schema='twentyone_pointwise_guard_signs_v1',remaining_raw_guard_indices=[i for i in previous if i not in removed],
        removed_guard_identities=[dict(raw_variable=i,contracted_variable=reverse[i],metadata=raw['variables'][i])for i in sorted(removed)],
        original_guard_indices=previous,
        prefix_proof=dict(initial_semantic_guard_indices=[i for i in previous if i<643],
            preliminary_t_n_bounds=load(BASE/'source/four_bounds.json')[:2],five_stages=prefix_stages,
            final_sign_steps=[step_for(36),step_for(37)],required_nonnegative_coordinates=list(range(643))),
        positive_prefix=dict(canonical_modulus_cut=canonical,initial_positive_coordinates=[4,5,129],
            steps=positive_steps,known_after=sorted(positive),required_seed_exponents=seed_k,
            independent_positive_bases=nonf0_bases),
        initial_A_D_bounds=load(BASE/'source/four_bounds.json')[2:],frame_arguments=args,frame_cut=frame,
        bootstrap_norm=bootstrap,unit_norm_cut=unit,comparison_base_constructor=Bconstructor,
        comparison_base_congruence=Bcongruence,positive_V_product=Vproduct,
        moduli=moduli,power_calls=powers,seeds=seeds,early_exact_value_call=1,
        pointwise_map=dict(body_values_changed=0,existing_guard_triples_copied=79,
            fresh_guard_triples=21,fresh_integer_witnesses=63,
            missing_target_guard_records=[g for g in old['guards']if g['raw_variable']in removed]),
        statement='All21 guard values are nonnegative at the original tuple. Auxiliary absolute values only parameterize ordinary Pell theorems. No source power semantics is invoked before index orientation except the separately justified pow1 value, after its seed has been oriented.')
    need(len(cert['remaining_raw_guard_indices'])==79 and len(powers)==21 and len(seeds)==15,'complete proposed source boundary')
    return enc(cert)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    data=generate();p=HERE/'CERTIFICATE.json'
    if args.check:need(p.read_bytes()==data,'whole deterministic dependency certificate')
    else:p.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,sha256=sha256(data).hexdigest()),indent=2))


if __name__=='__main__':main()
