#!/usr/bin/env python3
"""Literal raw and contracted private U/Z affine involution certificates."""
import argparse
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
    for n,h in pins['files'].items():need(sha256((ROOT/n).read_bytes()).hexdigest()==h,'frozen source '+n)
    spec=importlib.util.spec_from_file_location('frozen_poly_ops',ROOT/'candidates/retained-radius-bounds/check.py')
    b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
    raw=load(BASE/'source/raw_builder.json');body=load(BASE/'source/natural667.json')
    retained=load(BASE/'domain_certificate.json')['retained_raw_indices'];reverse={v:i for i,v in enumerate(retained)}
    old=load(ROOT/'candidates/projected-radius-mixed-signs/domain_certificate.json')
    other=set()
    for row in raw['rows']:
        for c,m in row['terms']:
            if 655 not in m:continue
            need(len(m)==2,'U occurs only quadratically')
            other.update(i for i in m if i!=655)
    need(len(other)==16,'all fifteen S quotients and one B quotient')
    umap={i:{(i,):-1}for i in sorted(other|{655})}
    zmap={645:{():-2,(645,):-1},646:{(646,):-1},648:{(648,):-1}}
    def substitute(p,mapping):
        out={}
        for m,c in p.items():
            term={():c}
            for v in m:term=b.mul(term,mapping.get(v,{(v,):1}))
            out=b.add(out,term)
        return out
    orbits=[]
    for name,mapping,target in [('U',umap,655),('Zminus1',zmap,645)]:
        contracted={reverse[v]:{tuple(reverse[i]for i in m):c for m,c in p.items()}
                    for v,p in mapping.items()if v in reverse}
        raw_signs=[];body_signs=[]
        for rows,mp,out in [(raw['rows'],mapping,raw_signs),(body['residuals'],contracted,body_signs)]:
            for row in rows:
                p=b.poly(row['terms']);image=substitute(p,mp)
                need(image==p or image=={m:-c for m,c in p.items()},'entire row is preserved up to sign')
                out.append(1 if image==p else -1)
        orbits.append(dict(name=name,target_raw_variable=target,target_contracted_variable=reverse[target],
            raw_affine_map=[dict(variable=v,metadata=raw['variables'][v],terms=[[c,list(m)]for m,c in sorted(p.items())])for v,p in mapping.items()],
            contracted_affine_map=[dict(variable=v,metadata=body['variables'][v],terms=[[c,list(m)]for m,c in sorted(p.items())])for v,p in sorted(contracted.items())],
            original_raw_row_signs=raw_signs,contracted_row_signs=body_signs))
    # Exact norm cut at W,A,Z, without expanding any source power array.
    p=b.poly(raw['rows'][603]['terms']);comb={603:{():1}}
    definitions={row['gate']:i for i,row in enumerate(raw['rows'])if row.get('gate')is not None}
    while True:
        options=[v for m in p for v in m if v not in{643,644,646}and v in definitions]
        if not options:break
        v=max(options);m=next(m for m in p if v in m);res=list(m);res.remove(v)
        multiplier={tuple(res):p[m]};rid=definitions[v]
        p=b.add(p,b.mul(multiplier,b.poly(raw['rows'][rid]['terms'])),-1)
        comb[rid]=b.add(comb.get(rid,{}),multiplier,-1)
    norm=dict(factorized_symbols=dict(W=643,A=644,Z=646,Zminus1=645),
        expanded_polynomial=[[c,list(m)]for m,c in sorted(p.items())],
        row_combination=[dict(row=i,multiplier=[[c,list(m)]for m,c in sorted(q.items())])for i,q in sorted(comb.items())if q],
        affine_Z_definition_row=594)
    certificate=dict(schema='two_private_sign_orbits_v1',orbits=orbits,
        previous_raw_guard_indices=[g['raw_variable']for g in old['guards']],
        remaining_raw_guard_indices=[g['raw_variable']for g in old['guards']if g['raw_variable']not in{645,655}],
        new_973_guard_triples=[g for g in old['guards']if g['raw_variable']in{645,655}],
        initial_bound_steps=load(BASE/'source/four_bounds.json'),bootstrap_norm=norm,
        statement='Normalize U by its sign involution and Zminus1 by its affine reflection. A>=2 excludes Z=0, so exactly two new Legendre triples suffice. All other guarded values and semantic-prefix coordinates are fixed.')
    return enc(certificate)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    data=generate();p=HERE/'CERTIFICATE.json'
    if args.check:need(p.read_bytes()==data,'entire deterministic orbit certificate')
    else:p.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,sha256=sha256(data).hexdigest()),indent=2))


if __name__=='__main__':main()
