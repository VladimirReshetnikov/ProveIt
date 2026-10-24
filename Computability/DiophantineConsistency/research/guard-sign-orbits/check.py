#!/usr/bin/env python3
"""Independent complete-row private-sign symmetries and normalization domain."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'candidates/projected-radius-mixed-bounds'


def need(ok,text):
    if not ok:raise ValueError(text)


def load(p):return json.loads(p.read_text())


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj


def verify(raw,body,restoration,old,cert,b,mixed,baseline):
    def atom(v):return{(v,):1}
    def substitute(p,mapping):
        out={}
        for m,c in p.items():
            term={():c}
            for v in m:term=b.mul(term,mapping.get(v,atom(v)))
            out=b.add(out,term)
        return out
    retained=restoration['retained_raw_indices'];reverse={v:i for i,v in enumerate(retained)}
    need([raw['variables'][v]for v in retained]==body['variables']and len(reverse)==667,
         'complete actual raw-to667 coordinate identities')
    previous=[g['raw_variable']for g in old['guards']]
    need(cert['previous_raw_guard_indices']==previous and len(previous)==102,'actual previous102 guards')
    remaining=[v for v in previous if v not in{645,655}]
    need(cert['remaining_raw_guard_indices']==remaining and len(remaining)==100,
         'exactly two private sign guards omitted')
    fresh=[g for g in old['guards']if g['raw_variable']in{645,655}]
    need(cert['new_973_guard_triples']==fresh,'exact six missing literal973 guard slots')
    need({0,694}<=set(remaining),'preliminary t0/T guard inputs retained')
    need(cert['initial_bound_steps']==load(BASE/'source/four_bounds.json'),'unchanged four lower-bound certificates')
    known={0:0,694:0}
    bounds=[baseline.bound_step(raw,s,known,b)for s in cert['initial_bound_steps']]
    need(known[644]==2,'A>=2 licensed before the Z normalization')
    restored,_=mixed.restoration(raw,body,restoration,set())
    results=[];maps=[]
    need([o['name']for o in cert['orbits']]==['U','Zminus1'],'two specified sign orbits')
    for orbit,target in zip(cert['orbits'],[655,645]):
        need(orbit['target_raw_variable']==target and orbit['target_contracted_variable']==reverse[target],
             'actual orbit target identities')
        mp={}
        for item in orbit['raw_affine_map']:
            v=item['variable'];need(v not in mp and 643<=v<1259 and item['metadata']==raw['variables'][v],
                 'unique private original-coordinate orbit support')
            p=b.poly(item['terms']);need(all(len(m)<=1 and all(0<=i<1259 for i in m)for m in p),'integer affine original map')
            mp[v]=p
        need(mp[target]==({(655,):-1}if target==655 else{():-2,(645,):-1}),
             'exact U sign reflection or centered Zminus1 reflection')
        if target==655:
            other={i for row in raw['rows']for c,m in row['terms']if 655 in m for i in m if i!=655}
            need(len(other)==16 and set(mp)==other|{655}and all(mp[v]=={(v,):-1}for v in mp),
                 'every actual U partner and no extra signed value')
        else:
            need(mp=={645:{():-2,(645,):-1},646:{(646,):-1},648:{(648,):-1}},
                 'exact bootstrap affine reflection and its two wires')
        contracted={reverse[v]:{tuple(reverse[i]for i in m):c for m,c in p.items()}
                    for v,p in mp.items()if v in reverse}
        entries=[dict(variable=v,metadata=body['variables'][v],terms=[[c,list(m)]for m,c in sorted(p.items())])
                 for v,p in sorted(contracted.items())]
        need(orbit['contracted_affine_map']==entries,'complete literal contracted affine map')
        for v,p in mp.items():need(substitute(p,mp)==atom(v),'entire original map is an involution')
        for v,p in contracted.items():need(substitute(p,contracted)==atom(v),'contracted map is an involution')
        for v in range(643):need(mp.get(v,atom(v))==atom(v),'every semantic-prefix value is fixed')
        for v in previous:
            if v!=target:need(mp.get(v,atom(v))==atom(v),'all other previous guarded values are fixed')
        for rows,mapping,signs in [(raw['rows'],mp,orbit['original_raw_row_signs']),
                                   (body['residuals'],contracted,orbit['contracted_row_signs'])]:
            need(len(signs)==len(rows)and all(s in[-1,1]for s in signs),'every row has exactly one sign')
            for row,sign in zip(rows,signs):
                p=b.poly(row['terms']);need(substitute(p,mapping)=={m:sign*c for m,c in p.items()},
                     'complete original-row affine symmetry identity')
        for v,p in restored.items():
            need(substitute(p,contracted)==substitute(mp.get(v,atom(v)),restored),
                 'all1259 raw restoration recipes commute with the orbit')
        results.append(dict(name=orbit['name'],raw_moved_coordinates=len(mp),contracted_moved_coordinates=len(contracted),
            full_raw_row_identities=1177,full_contracted_row_identities=585,
            negated_raw_rows=[i for i,s in enumerate(orbit['original_raw_row_signs'])if s==-1],
            negated_contracted_rows=[i for i,s in enumerate(orbit['contracted_row_signs'])if s==-1],
            commuting_raw_restoration_identities=1259,fixed_other_guard_values=101))
        maps.append(mp)
    for v in set(maps[0])|set(maps[1]):
        need(substitute(maps[0].get(v,atom(v)),maps[1])==substitute(maps[1].get(v,atom(v)),maps[0]),
             'the two affine involutions commute')
    norm=cert['bootstrap_norm'];need(norm['factorized_symbols']==dict(W=643,A=644,Z=646,Zminus1=645),
         'literal bootstrap norm symbols')
    w,a,z=atom(643),atom(644),atom(646)
    expected=b.add(b.add(b.mul(a,a),{():1},-1),b.mul(b.mul(b.mul(w,w),b.mul(w,b.add(w,{():2}))),b.mul(z,z)),-1)
    need(b.poly(norm['expanded_polynomial'])==expected,'full bootstrap norm A²-1-W³(W+2)Z²')
    actual={}
    for item in norm['row_combination']:
        i=item['row'];need(type(i)is int and 0<=i<1177,'original bootstrap ideal row')
        multiplier=b.poly(item['multiplier']);need(all(0<=v<1259 for m in multiplier for v in m),'bootstrap ideal coordinates')
        actual=b.add(actual,b.mul(multiplier,b.poly(raw['rows'][i]['terms'])))
    need(actual==expected,'complete bootstrap norm original-row identity')
    need(norm['affine_Z_definition_row']==594 and b.poly(raw['rows'][594]['terms'])==
         {(646,):1,():-1,(645,):-1},'actual Z=Zminus1+1 row')
    at_zero={m:c for m,c in expected.items()if 646 not in m}
    need(at_zero=={(644,644):1,():-1},'Z=0 forces A²=1')
    strict=b.nonnegative(at_zero,{644:2},True)
    return dict(initial_guard_count=100,recovered_previous_guard_count=102,preliminary_bounds=bounds,
        orbit_certificates=results,commuting_orbits=True,
        excluded_Z_zero_shifted_polynomial=[[c,list(m)]for m,c in sorted(strict.items())],
        fresh_existential_legendre_witnesses=6,
        new_973_guard_triples=fresh,
        semantic_prefix_values_changed=0,
        statement='Apply U reflection iff U<0. A>=2 excludes Zminus1=-1; apply Z reflection iff Zminus1<=-2. All100 retained guarded values stay fixed; then choose six new guard witnesses into literal973.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(sha256((ROOT/n).read_bytes()).hexdigest()==h,'whole frozen dependency '+n)
    for name in ['projected-radius-mixed-signs','projected-radius-mixed-bounds']:
        folder=ROOT/'candidates'/name;files=load(folder/'MANIFEST.json')['files']
        need({str(p.relative_to(folder))for p in folder.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}==set(files),'closed whole frozen foundation')
        for n,h in files.items():need(sha256((folder/n).read_bytes()).hexdigest()==h,'sealed whole foundation member '+n)
    raw=load(BASE/'source/raw_builder.json');body=load(BASE/'source/natural667.json')
    restoration=load(BASE/'source/raw_restoration.json')
    old=load(ROOT/'candidates/projected-radius-mixed-signs/domain_certificate.json');cert=load(HERE/'CERTIFICATE.json')
    b=module('frozen_nonnegative_polynomial_checker',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed=module('frozen_integer_affine_restoration',ROOT/'candidates/projected-radius-mixed/check.py')
    baseline=module('frozen_four_original_bounds',BASE/'check.py')
    result=verify(raw,body,restoration,old,cert,b,mixed,baseline);mutations=[]
    def reject(label,thunk):
        try:thunk()
        except(ValueError,RuntimeError,KeyError,IndexError,TypeError):mutations.append(label)
        else:raise ValueError('false symmetry accepted '+label)
    bad=deepcopy(cert);bad['orbits'][0]['raw_affine_map'].pop()
    reject('one U partner sign omitted',lambda:verify(raw,body,restoration,old,bad,b,mixed,baseline))
    bad=deepcopy(cert);bad['orbits'][1]['raw_affine_map'][0]['terms'][0][0]=-1
    reject('wrong affine reflection center',lambda:verify(raw,body,restoration,old,bad,b,mixed,baseline))
    bad=deepcopy(cert);bad['orbits'][1]['original_raw_row_signs'][594]=1
    reject('missing row negation',lambda:verify(raw,body,restoration,old,bad,b,mixed,baseline))
    bad=deepcopy(cert);bad['bootstrap_norm']['expanded_polynomial'][0][0]+=1
    reject('changed bootstrap norm coefficient',lambda:verify(raw,body,restoration,old,bad,b,mixed,baseline))
    bad=deepcopy(cert);bad['initial_bound_steps'][2]['lower']=1
    reject('unlicensed A bound weakening',lambda:verify(raw,body,restoration,old,bad,b,mixed,baseline))
    bad=deepcopy(cert);bad['new_973_guard_triples'][0]['auxiliary'][0]+=1
    reject('wrong literal973 new guard slot',lambda:verify(raw,body,restoration,old,bad,b,mixed,baseline))
    result.update(status='PASS',optimized_python=bool(sys.flags.optimize),rejected_corruptions=mutations,
        scope='Universal affine symmetries and exact sign-domain normalization only. No new full quartic/frontier is materialized here; no arithmetic semantic transfer or Lean claim.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
