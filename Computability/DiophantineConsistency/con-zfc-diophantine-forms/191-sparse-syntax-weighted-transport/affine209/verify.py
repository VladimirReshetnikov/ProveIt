#!/usr/bin/env python3
"""Independent finite checks; no import of the producer and no zero search."""
from pathlib import Path
from collections import defaultdict
from math import comb
import hashlib,json

ROOT=Path(__file__).resolve().parent
def require(ok,description):
    if not ok:raise ValueError(description)
def read(path):return json.loads((ROOT/path).read_text())
def p(ts):return {tuple(m):c for c,m in ts}
def add(a,b,k=1):
    z=dict(a)
    for mon,c in b.items():z[mon]=z.get(mon,0)+k*c
    return {m:c for m,c in z.items() if c}
def names(e):return [v['name'] for v in e['variables']]
def horizon(e):
    r=[i for i,x in enumerate(e['residuals']) if x['label']=='cofinal.horizon']
    require(len(r)==1,'one horizon');return r[0]

def protection():
    source=read('source/source216.json')
    t=names(source).index('t0');z=names(source).index('cofinal.horizon_root');h=horizon(source)
    n=len(source['variables']);checks=[]
    for step in read('source/projection211_certificate.json')['steps']:
        direction=dict(step['direction']);pivot=step['pivot'];row=step['deleted_row']
        require(direction.get(t,0)==direction.get(z,0)==0,'radical touches protected variable')
        require(pivot not in (t,z) and row!=h,'radical deletes protected variable/row')
        require(all(t not in m and z not in m for _,m in step['sheared_pivot_solution']), 'restoration touches horizon')
        kept=step['retained_old_indices'];require(kept==[i for i in range(n) if i!=pivot],'radical renumbering')
        t=kept.index(t);z=kept.index(z);h-=row<h;n-=1;checks.append('protected radical')
    e=read('source/projection211.json')
    require((t,z,h)==(names(e).index('t0'),names(e).index('cofinal.horizon_root'),horizon(e)),'first endpoint tracking')
    cert=read('source/projection210_certificate.json');pivot=cert['eliminated_coordinate'];row=cert['omitted_residual']
    require(pivot not in (t,z) and row!=h,'affine projection protection')
    require(all(j!=h for _,j in cert['affine_consequence']['row_combination']),'affine uses horizon row')
    require(all(t not in m and z not in m for _,m in cert['restoration_terms_original_indices']),'affine solution uses horizon')
    t-=pivot<t;z-=pivot<z;h-=row<h
    e=read('source/projection210.json')
    require((t,z,h)==(names(e).index('t0'),names(e).index('cofinal.horizon_root'),horizon(e)),'second endpoint tracking')
    cert=read('source/final210_certificate.json')
    for op in cert['operations']:
        if op['type']=='coordinate':
            require(op['coordinate'] not in (t,z),'coordinate changes protected input')
            require(all(t not in m and z not in m for _,m in op['image']),'coordinate mixes horizon')
        elif op['type']=='row':require(op['source']!=h and op['target']!=h,'row operation mixes horizon')
        else:raise ValueError('unknown operation')
    e=read('source/parent210.json')
    require((t,z,h)==(names(e).index('t0'),names(e).index('cofinal.horizon_root'),horizon(e)),'final endpoint tracking')
    return {'radical_projections':len(checks),'affine_projections':1,'elementary_operations':len(cert['operations']),'protected_old_indices':[t,z,h]}

def independent_substitution(ts,t,z,minimum):
    out=defaultdict(int)
    for c,mon in ts:
        count=mon.count(t);other=[i for i in mon if i!=t]
        for j in range(count+1):
            out[tuple(sorted(other+[z]*j))]+=c*comb(count,j)*minimum**(count-j)*(2*minimum)**j
    return {m:c for m,c in out.items() if c}

def sos(rows):
    out=defaultdict(int)
    for ts in rows:
        for i,(c,m) in enumerate(ts):
            for j in range(i,len(ts)):
                d,n=ts[j];out[tuple(sorted(m+n))]+=c*d*(1 if i==j else 2)
    return {m:c for m,c in out.items() if c}

def check(minimum):
    folder=Path('profiles')/('minimum'+str(minimum));e=read(folder/'equation.json');old=read('source/parent210.json')
    t=names(old).index('t0');z=names(old).index('cofinal.horizon_root');h=horizon(old)
    kept=[i for i in range(len(old['variables'])) if i!=t];ren={j:i for i,j in enumerate(kept)}
    expected=[]
    for i,r in enumerate(old['residuals']):
        if i==h:continue
        q=independent_substitution(r['terms'],t,z,minimum)
        expected.append({tuple(ren[j] for j in mon):c for mon,c in q.items()})
    require(expected==[p(r['terms']) for r in e['residuals']],'literal affine substitution')
    require(len(e['variables'])==209 and len(expected)==149,'dimension/row count')
    require(max(len(m) for row in expected for m in row)==2,'residual degree')
    live={i for row in expected for mon in row for i in mon};require(live==set(range(209)),'input liveness')
    pol=sos([r['terms'] for r in e['residuals']])
    require(pol==p(read(folder/'expanded_polynomial.json')['terms']),'independent expanded coefficients')
    met=read(folder/'metrics.json')
    recomputed={'variables':209,'rows':149,'degree':max(map(len,pol)),'monomials':len(pol),
                'height':max(map(abs,pol.values())), 'row_height':max(abs(c) for row in expected for c in row.values()),
                'residual_monomials':sum(len(row) for row in expected)}
    require(met==recomputed,'metrics')
    # Exact nonzero square coefficient proves degree after collection.
    require(recomputed['degree']==4,'quartic attained')
    # Every certificate is an actual definition of the inverse map.
    cert=read(folder/'certificate.json')
    require(cert['kept_old_indices']==kept,'projection chart')
    require(p(cert['restore_t'])=={():minimum,(ren[z],):2*minimum},'inverse horizon')
    require(cert['output_sha256']==hashlib.sha256((ROOT/folder/'equation.json').read_bytes()).hexdigest(),'final binding')
    # Finite semantic diagnostics are supplementary, never consistency searches.
    for j in range(-20,21):
        horizon_value=minimum*(2*j+1)
        require(horizon_value!=0 and abs(horizon_value)>=minimum,'affine progression')
    return met

def main():
    ledger=read('SOURCES.json')
    for fn,sha in ledger['source_files'].items():require(hashlib.sha256((ROOT/fn).read_bytes()).hexdigest()==sha,('source binding',fn))
    result={'protection':protection(),'profiles':{str(m):check(m) for m in (16,8,2)}}
    # Verify rejection of representative producer-independent artifact damage.
    original=read('source/parent210.json');damaged=json.loads(json.dumps(original))
    h=horizon(damaged);damaged['residuals'][h]['label']='other'
    rejected=False
    try:horizon(damaged)
    except ValueError:rejected=True
    require(rejected,'horizon mutation negative control')
    result['negative_controls']=1
    print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
