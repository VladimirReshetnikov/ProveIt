#!/usr/bin/env python3
"""Build a quartic using delayed recovery of power-quotient signs.

Only local immutable inputs are read.  The delivered equation is rebuilt in
the requested output directory.  No search for a zero or theorem prover runs.
"""
from pathlib import Path
from collections import Counter,defaultdict
from functools import lru_cache
import argparse,copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
import terminal_elimination as te

def need(ok,msg):
    if not ok:raise ValueError(msg)
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def poly(terms):return {tuple(m):c for c,m in terms if c}
def scale(p,c):return {m:a*c for m,a in p.items() if a*c}
def sqroot(p):
    from math import isqrt
    diag=sorted((m[0],c) for m,c in p.items() if len(m)==2 and m[0]==m[1] and c>0)
    if not diag:return None
    v,c=diag[0];r=isqrt(c)
    if r*r!=c:return None
    out={(v,):r}
    for u in sorted({u for m in p for u in m}-{v}):
        val=p.get(tuple(sorted((u,v))),0)
        if val%(2*r):return None
        if val:out[(u,)]=val//(2*r)
    val=p.get((v,),0)
    if val%(2*r):return None
    if val:out[()]=val//(2*r)
    return out if te.multiply(out,out)==p else None
def conditions(p,strict=False):
    if any(c<0 for m,c in p.items() if m):return []
    req={(v,0) for m in p for v,k in Counter(m).items() if k%2}
    lower=p.get((),0);target=int(strict)
    if lower>=target:return [req]
    return [req|{(v,1) for v in m} for m,c in p.items() if m and c+lower>=target]
def rules_from(eq):
    rules=[]
    for rid,row in enumerate(eq['residuals']):
        p=poly(row['terms'])
        for v in sorted({v for m in p for v in m}):
            if any(m.count(v)>1 for m in p):continue
            a={tuple(i for i in m if i!=v):c for m,c in p.items() if v in m}
            b={m:-c for m,c in p.items() if v not in m}
            for s in (1,-1):
                aa,bb=scale(a,s),scale(b,s)
                for ca in conditions(aa,True):
                    for strict in (0,1):
                        for cb in conditions(bb,bool(strict)):
                            req=ca|cb
                            if (v,strict) not in req:
                                rules.append({'target':[v,strict],'requires':req,'row':rid,'sign':s,'kind':'positive_factor'})
                if len(aa)==1 and aa.get((),0)>0:
                    root=sqroot(bb)
                    if root is not None:
                        rules.append({'target':[v,0],'requires':set(),'row':rid,'sign':s,'kind':'affine_square','square_root':te.as_terms(root)})
    for v in range(len(eq['variables'])):
        rules.append({'target':[v,0],'requires':{(v,1)},'row':None,'sign':1,'kind':'strict_to_weak'})
    return rules
def close(known,rules):
    known=set(known);history=[]
    while True:
        changed=False
        for r in rules:
            key=tuple(r['target'])
            if key not in known and r['requires']<=known:
                known.add(key);changed=True
                history.append({k:v for k,v in r.items() if k!='requires'})
        if not changed:return known,history

def build(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    source=json.loads((ROOT/'upstream/source690/equation.json').read_text())
    raw=json.loads((ROOT/'upstream/source690/gate_ledger.json').read_text())
    interface=json.loads((ROOT/'upstream/source690/interface.json').read_text())
    parameters=json.loads((ROOT/'parameters.json').read_text())
    names={v['name']:i for i,v in enumerate(source['variables'])}
    rn={i:v['name'] for i,v in enumerate(raw['all_variables'])}
    def mapped(a):
        need(a[0]=='v' and rn[a[1]] in names,'semantic target must be retained')
        return names[rn[a[1]]]
    guards=parameters['guards'];rules=rules_from(source)
    known,pre=close({(v,0) for v in guards},rules)
    framefacts=[(mapped(b['T']),1) for b in interface['bases']]+[(mapped(interface['frame']['D']),1)]
    known,mid=close(known|set(framefacts),rules)
    powerfacts=[(mapped(p['h']),0) for p in interface['powers']]
    known,post=close(known|set(powerfacts),rules)
    need(all((i,0) in known for i in range(len(names))),'domain recovery incomplete')
    cert={'schema':'delayed_power_signs_v1','source_sha256':hashlib.sha256(canonical(source)).hexdigest(),
          'guards':guards,'pre_steps':pre,'frame_facts':framefacts,'middle_steps':mid,
          'power_facts':powerfacts,'post_steps':post,'source_variables':len(names)}
    signed=copy.deepcopy(source);signed['domain']='unrestricted integers';signed.pop('metrics',None)
    for v in guards:
        a,b,c=range(len(signed['variables']),len(signed['variables'])+3)
        signed['variables'] += [{'name':f'nonnegative.{v}.{s}','kind':'integer_guard'} for s in ['a','b','c']]
        signed['residuals'].append({'label':f'nonnegative.{v}',
              'terms':te.as_terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    target,projection,metrics=te.optimize(signed,max_support=parameters['max_support'])
    metrics['guard_count']=len(guards);metrics['original_natural_variables']=len(names)
    te.verify(signed,target,projection)
    for name,value in [('domain_certificate.json',cert),('signed_source.json',signed),
                       ('equation.json',target),('projection.json',projection),
                       ('expanded_polynomial.json',te.expand(target)),('METRICS.json',metrics)]:
        (out/name).write_bytes(canonical(value))
    return metrics
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();print(json.dumps(build(args.output),indent=2,sort_keys=True))
