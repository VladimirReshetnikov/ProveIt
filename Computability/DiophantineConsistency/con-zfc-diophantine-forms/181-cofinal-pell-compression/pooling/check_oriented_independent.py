#!/usr/bin/env python3
"""Independent exact finite audit of the oriented power-pool equations.

No producer code is imported. The input residuals define the polynomial;
the unbounded power theorem is reviewed separately.
"""
import argparse, collections, hashlib, json, shutil, tempfile
from pathlib import Path

def require(condition,message):
    if not condition: raise ValueError(message)
def clean(p): return {m:a for m,a in p.items() if a}
def read(p):
    r=collections.defaultdict(int)
    for a,m in p:r[tuple(sorted(m))]+=a
    return clean(r)
def plus(*ps):
    r=collections.defaultdict(int)
    for p in ps:
        for m,a in p.items():r[m]+=a
    return clean(r)
def times(*ps):
    r={():1}
    for p in ps:
        z=collections.defaultdict(int)
        for m,a in r.items():
            for n,b in p.items():z[tuple(sorted(m+n))]+=a*b
        r=clean(z)
    return r
def const(a):return {():a} if a else {}
def var(i):return {(i,):1}
def neg(p):return {m:-a for m,a in p.items()}
def minus(p,q):return plus(p,neg(q))
def sq(p):return times(p,p)
def substitute(p,mapping):
    z=collections.defaultdict(int)
    for mon,a in p.items():
        if not any(i in mapping for i in mon):z[mon]+=a;continue
        term=times(const(a),*(mapping.get(i,var(i)) for i in mon))
        for m,b in term.items():z[m]+=b
    return clean(z)
def compress(p,keep):
    mp={i:j for j,i in enumerate(keep)}
    require(all(i in mp for m in p for i in m),'removed coordinate survives')
    return {tuple(mp[i] for i in m):a for m,a in p.items()}
def degree(p):return max(map(len,p),default=-1)
def load(path):return json.loads(path.read_text())

def audit(source,folder):
    parent=load(source);old=[read(r['terms']) for r in parent['residuals']]
    cert=load(folder/'certificate.json');split=cert['split']
    require(hashlib.sha256(source.read_bytes()).hexdigest()==cert['source_sha256'],'source hash')
    deleted={102,103,104,105,106,107,153,154,155,156}
    private={145,146,147,148,149,150,215,216,217,218}
    require(set(cert['deleted_rows'])==deleted and set(cert['private_coordinates'])==private,'deleted interface')
    require(all(not private.intersection(m) for i,r in enumerate(old) if i not in deleted for m in r),'private occurrence')
    A=plus(var(138),const(1))
    bases=[var(0),var(3),var(190),minus(var(101),const(1)),var(101)]
    T=[minus(minus(times(const(2),A,n),sq(n)),const(1)) for n in bases]
    E=[]
    single=[(var(2),var(187),var(188),var(189)),(var(17),var(178),var(179),plus(var(180),const(1))),
            (minus(var(101),const(1)),var(178),var(179),plus(var(180),const(1)))]
    for j,(m,D,Y,Z) in enumerate(single):
        delta=minus(minus(m,D),times(bases[j],Y))
        e=plus(sq(delta),times(T[j],sq(Y)),times(const(2),bases[j],Y,minus(Z,times(A,Y))))
        require(degree(e)<=3,'singleton cubic cancellation')
        E.append(e)
        modulus_row=minus(var(145+2*j),T[j])
        require(old[102+2*j] in (modulus_row,neg(modulus_row)),'literal singleton modulus')
        error_row=plus(delta,times(var(145+2*j),var(146+2*j)))
        require(old[103+2*j] in (error_row,neg(error_row)),'literal singleton error')
    for j,k,l,a,b in [(3,217,218,155,156),(4,215,216,153,154)]:
        comb=plus(old[b],times(bases[j],old[a]));e=plus(comb,times(T[j],var(l)))
        require(all(k not in m and l not in m for m in e),'pool private cancellation')
        E.append(e)
    require([read(x) for x in cert['T_parent_chart']]==T,'all modulus coefficients')
    require([read(x) for x in cert['E_parent_chart']]==E,'all error coefficients')
    def oriented(ids,z):
        return minus(plus(*(times(bases[i],E[i],*(T[h] for h in ids if h!=i)) for i in ids)),times(var(z),*(T[i] for i in ids)))
    if split:
        added=[oriented(range(3),221),minus(plus(times(E[3],T[4]),times(E[4],T[3])),times(var(222),T[3],T[4]))]
    else:added=[oriented(range(5),221)]
    keep=[i for i in range(222+int(split)) if i not in private]
    rows=[compress(r,keep) for i,r in enumerate(old) if i not in deleted]+[compress(r,keep) for r in added]
    raw=load(folder/('raw213.json' if split else 'raw212.json'))
    require(rows==[read(r['terms']) for r in raw['residuals']],'entire raw polynomial rows')
    names=[v['name'] for v in raw['variables']]
    n=len(names)
    # Directly expand each integer shear; do not use the producer's
    # directional-derivative implementation.
    for step in cert['radical_steps']:
        p=step['pivot'];d=dict(step['direction']);ri=step['deleted_row']
        require(d[p]==1,'unit shear pivot')
        mapping={i:plus(var(i),times(const(a),var(p))) for i,a in d.items() if i!=p}
        sheared=[substitute(r,mapping) for r in rows]
        require(all(sum(i==p for i in m)<=1 and (p not in m or len(m)==1) for r in sheared for m in r),'shear not linear with constant slope')
        slope=sheared[ri].get((p,),0)
        require(slope in (-1,1) and slope==step['slope'],'pivot slope')
        restore=times(const(-slope),substitute(sheared[ri],{p:{}}))
        require(restore==read(step['restoration_terms']),'actual pivot restoration')
        transformed=[substitute(r,{p:restore}) for r in sheared]
        require(not transformed[ri],'restored pivot row')
        keep=[i for i in range(n) if i!=p]
        require(keep==step['retained_old_indices'],'retained projection indices')
        rows=[compress(r,keep) for i,r in enumerate(transformed) if i!=ri]
        names=[names[i] for i in keep];n-=1
    a=cert['affine_step'];p=a['pivot'];restore=read(a['restoration_terms'])
    comb=plus(*(times(const(k),rows[i]) for k,i in a['row_combination']))
    require(comb==minus(var(p),restore) or comb==minus(restore,var(p)),'unit affine consequence')
    imgs=[substitute(r,{p:restore}) for r in rows];omit=a['omitted_row']
    require(any(r==imgs[omit] for i,r in enumerate(imgs) if i!=omit),'omitted affine row not restored')
    keep=[i for i in range(n) if i!=p]
    require(keep==a['retained_old_indices'],'affine retained indices')
    rows=[compress(r,keep) for i,r in enumerate(imgs) if i!=omit];names=[names[i] for i in keep]
    final=load(folder/('principal207.json' if split else 'principal206.json'))
    require(rows==[read(r['terms']) for r in final['residuals']],'all final residual coefficients')
    require(names==[v['name'] for v in final['variables']],'all variable identities')
    live={i for r in rows for m in r for i in m}
    require(live==set(range(len(names))),'final coordinate liveness')
    hist=collections.Counter(degree(r) for r in rows)
    metrics={'variables':len(names),'residuals':len(rows),'degree':2*max(hist),'residual_degree_histogram':dict(sorted(hist.items())),
             'residual_monomials':sum(len(r) for r in rows),'maximum_residual_coefficient':max(abs(a) for r in rows for a in r.values())}
    # A nonzero top degree exists literally, and the sum of squares of
    # leading homogeneous forms is nonzero over R.
    require(metrics['degree']==(16 if split else 24),'exact degree')
    if split:
        expanded=plus(*(sq(r) for r in rows))
        frozen=load(folder/'expanded_polynomial.json')
        require(expanded==read(frozen['terms']),'every expanded polynomial coefficient')
        require(frozen['variables']==len(names),'expanded variable count')
        metrics['expanded_monomials']=len(expanded)
        metrics['expanded_coefficient_height']=max(abs(a) for a in expanded.values())
    return metrics

def corruption_controls(source,folder):
    rejected=[]
    for mode in ('pooled_coefficient','omitted_retained_row','pivot_restoration'):
        with tempfile.TemporaryDirectory(prefix='oriented-independent-') as td:
            work=Path(td)/'candidate';shutil.copytree(folder,work)
            if mode=='pivot_restoration':
                p=work/'certificate.json';obj=load(p)
                obj['radical_steps'][0]['restoration_terms'][0][0]+=1
            else:
                p=work/'raw212.json';obj=load(p)
                if mode=='pooled_coefficient':obj['residuals'][-1]['terms'][0][0]+=1
                else:obj['residuals'].pop(0)
            p.write_text(json.dumps(obj))
            try:audit(source,work)
            except ValueError as error:rejected.append({'control':mode,'rejection':str(error)})
            else:raise ValueError('corruption accepted: '+mode)
    return rejected

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    local=Path(__file__).resolve().parent
    default=local if (local/'173-crt-index-anchor-215/source/anchor221/equation.json').is_file() else local.parent/'research_direct'
    parser.add_argument('--root',type=Path,default=default)
    parser.add_argument('--source',type=Path)
    parser.add_argument('--candidate',type=Path,action='append')
    parser.add_argument('--skip-corruption-controls',action='store_true')
    args=parser.parse_args()
    source=args.source or args.root/'173-crt-index-anchor-215/source/anchor221/equation.json'
    folders=args.candidate or [args.root/'oriented_pool',args.root/'oriented_split']
    controls=[]
    control_folder=next((p for p in folders if (p/'raw212.json').exists()),None)
    if control_folder and not args.skip_corruption_controls:controls=corruption_controls(source,control_folder)
    print(json.dumps({'status':'pass','profiles':{p.name:audit(source,p) for p in folders},'rejected_corruptions':controls,
       'scope':'Exact source replacement, all shear/restoration identities, all final coefficients and counts; unbounded arithmetic proof reviewed separately.'},indent=2))
