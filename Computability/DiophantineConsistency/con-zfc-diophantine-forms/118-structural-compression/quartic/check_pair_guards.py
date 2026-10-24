#!/usr/bin/env python3
"""Independent exact source cuts, domains, signed restorations and full SOS.

Does not import the producer or optimizer. Integer polynomial algebra below
is independent of the equation producer. The upstream independent projection
checker replays every monic row deletion and substitution.
"""
from pathlib import Path
from collections import defaultdict
from copy import deepcopy
import json,sys,hashlib
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'))
from verify_projection import verify

def need(b,s):
    if not b:raise ValueError(s)
def load(name):return json.loads((HERE/name).read_text())
def poly(terms):
    out=defaultdict(int)
    for c,m in terms:out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items()if c}
def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items()if c}
def neg(p):return {m:-c for m,c in p.items()}
def sos(equation):
    out=defaultdict(int)
    for row in equation['residuals']:
        p=poly(row['terms'])
        need(all(len(m)<=2 for m in p),'quadratic residual')
        for m,c in p.items():
            for n,d in p.items():out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items()if c}

def check_domain(family,newpath):
    old=load(f'factorial-radius-output-sign-profile_{family}_parent.json')
    dom=load(f'factorial-radius-output-sign-profile_{family}_domain.json')
    new=load(newpath+'/parent.json');nd=load(newpath+'/domain.json')
    cert=load('PAIR_GUARD_CERTIFICATE.json');pairs=cert['pairs']
    n,nr=dom['baseline_body_variables'],dom['baseline_body_rows']
    mp={v:i for i,v in enumerate(dom['baseline_raw_indices'])}
    need(old['domain']==new['domain']=='unrestricted integers','domain')
    need(new['variables'][:n]==old['variables'][:n]and new['residuals'][:nr]==old['residuals'][:nr],'whole unchanged source body')
    removed={p[k]for p in pairs for k in['r','s']}
    oldpred=[g['predicate']for g in dom['guards']]
    retained=[p for p in oldpred if not(p['kind']=='retained_scalar'and p['raw_variables'][0]in removed)]
    need(len(oldpred)==75 and len(retained)==63 and len(removed)==12,'precise 12-to-6 predicate cut')
    expected=retained+[dict(kind='shared_modulus_pair',raw_variables=[p['r'],p['s']],terms=[[1,[mp[p['r']],mp[p['s']]]]])for p in pairs]
    need([g['predicate']for g in nd['guards']]==expected,'all new predicates')
    retained_scalar={p['raw_variables'][0]for p in retained if p['kind']=='retained_scalar'}
    identities=[]
    for p in pairs:
        for kind,x,y in [('target',p['r'],p['s']),('anchor',p['a'],p['b'])]:
            ids=p[family+'_'+kind+'_rows']
            got=add(*(poly(old['residuals'][i]['terms'])for i in ids))
            wanted=poly([[1,[mp[p['B']]]],[-1,[mp[x]]],[-1,[mp[y]]],[-1,[]]])
            need(got==wanted or got==neg(wanted),'complete actual source-row '+kind+' identity')
        need(p['a']in retained_scalar and p['b']in retained_scalar,'both anchor predicates retained before semantics')
        identities.append(dict(r=p['r'],s=p['s'],B=p['B'],anchor=[p['a'],p['b']]))
    need(len(nd['guards'])==69 and len(new['variables'])==n+3*69 and len(new['residuals'])==nr+69,'actual new dimensions')
    for j,(g,p)in enumerate(zip(nd['guards'],expected)):
        a,b,c=range(n+3*j,n+3*j+3)
        need(g['auxiliary']==[a,b,c],'fresh guard triple')
        want=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]
        need(new['residuals'][nr+j]['terms']==want,'whole guard row')
        need(new['variables'][a:c+1]==[dict(kind='nonnegative_guard',name=f'pair69_guard.{j}.{s}')for s in['a','b','c']],'guard metadata')
    return new,dict(source_variables=n,source_rows=nr,predicates=69,identities=identities,restored_old_predicates=75)

def main():
    for item in load('SOURCE_PROVENANCE.json')['files']:
        raw=(HERE/item['local']).read_bytes()
        need(hashlib.sha256(raw).hexdigest()==item['sha256'],'whole copied source '+item['local'])
        need(hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()==item['git_blob_sha'],'immutable Git source '+item['local'])
    parents={};domains={}
    for family,name in [('raw','pair69'),('compact','pair69_compact')]:
        parents[name],domains[name]=check_domain(family,name)
    configs=['pair69/support8','pair69/support16','pair69/support32','pair69_compact/support32','pair69/support16_affine2','pair69/support32_quadratic_first']
    outcomes={}
    for name in configs:
        e=load(name+'/equation.json');cert=load(name+'/projection.json');p=load(name+'/polynomial.json')
        r=verify(parents[name.split('/')[0]],e,cert)
        need(cert['unconstrained_removed']==[],'every lost coordinate has an exact integer restoration')
        got=sos(e);need(got==poly(p['terms']),'every collected quartic coefficient')
        metrics=dict(variables=len(e['variables']),quadratic_rows=len(e['residuals']),degree=max(map(len,got)),monomials=len(got),height=max(map(abs,got.values())))
        need(metrics['degree']==4,'exact quartic')
        need(p['variables']==metrics['variables']and p['domain']=='unrestricted integers','full quartic domain and arity')
        outcomes[name]=dict(**metrics,projection=r)
        print(name,metrics,flush=True)
    # These controls inspect essential semantic cuts, not random evaluations.
    bad=load('PAIR_GUARD_CERTIFICATE.json');bad['pairs'][0]['raw_target_rows'][0]+=1
    old=load('factorial-radius-output-sign-profile_raw_parent.json');p=bad['pairs'][0]
    badsum=add(*(poly(old['residuals'][i]['terms'])for i in p['raw_target_rows']))
    target=poly([[1,[p['B']]],[-1,[p['r']]],[-1,[p['s']]],[-1,[]]])
    need(badsum not in [target,neg(target)],'changed source-row certificate rejected')
    badpoly=deepcopy(load('pair69/support8/polynomial.json'));badpoly['terms'][0][0]+=1
    need(sos(load('pair69/support8/equation.json'))!=poly(badpoly['terms']),'changed full quartic coefficient rejected')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),domains=domains,profiles=outcomes,negative_controls=['changed source-row identity','changed full quartic coefficient'],scope='Exact algebra and ordinary 69-to-75 source domain reduction; C222/refutation calibration inherited; no new internal-ZFC or Lean certificate.')
    (HERE/'CHECK_PAIR_GUARDS.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(outcomes)),indent=2))

if __name__=='__main__':main()
