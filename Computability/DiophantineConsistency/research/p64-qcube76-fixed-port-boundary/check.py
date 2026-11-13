#!/usr/bin/env python3
"""Check a conditional fixed-port boundary transformation, not a zero witness."""
import hashlib,json,random,runpy,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent; root=here.parents[3]
oldpath=here.parent/'p64-qcube77-candidate/graph.json'
newpath=here.parent/'p64-qcube76-transport-candidate/graph.json'
verify=root/'Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/positive14/verify.py'
pins={oldpath:'8cda8e5729f7af6b725631a0a9a5b5d8886c24a4e62d94d889ada47ce54e7315',newpath:'58b259ef212dded883ef0e36aedad303d07dad5ae00d7b1c6674ce4178a09de8',verify:'97de6a4ff04997de2c5e0062c4c8b335cf4c8da6b1cd2b85b543948a62e3677b'}
for p,h in pins.items():
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h: raise RuntimeError('input drift: '+str(p))
old=json.loads(oldpath.read_text()); new=json.loads(newpath.read_text()); Poly=runpy.run_path(str(verify))['Poly']
q,F,a,K,w,z,d,h=map(Poly.var,('q','F','alpha','K','w','z','d','h'))
C=q-F-a; F2=F-d; C2=C+q*d; z2=z+d*(K+w)+h
old_gap=(q-1)*(q-F)+a; new_gap=q*(q-F2)-C2
old_lt=(K+w)*C-F-z*(q-1); new_lt=(K+w)*C2-F2-z2*(q-1)
if old_gap!=new_gap: raise RuntimeError('gap identity failure')
if new_lt-old_lt != d*(K+w+1)-h*(q-1): raise RuntimeError('transport identity failure')
if C2-(q-F2) != d*(q-1)-a: raise RuntimeError('strict-bound identity failure')
def evaluate(rows,initial,mod):
    x={n:v%mod for n,v in initial.items()}
    def get(v): return v%mod if isinstance(v,int) else x[v]
    for name,op,a,b in rows:
        u,v=get(a),get(b)
        x[name]={'+':lambda:(u+v)%mod,'-':lambda:(u-v)%mod,'*':lambda:(u*v)%mod}[op]()
    return x
rng=random.Random(0x76F1); samples=0
for mod in (1000003,1000033,1000037):
    for _ in range(200):
        beta=rng.randint(1,8); J=rng.randint(3,12); qv=beta*J+1
        Fv=rng.randint(2,qv-2); av=rng.randint(1,qv-Fv-1); Cv=qv-Fv-av
        Kv=rng.randint(0,30); wv=(-Kv-1)%(qv-1) or qv-1
        hv=(Kv+wv+1)//(qv-1)
        sample={name:rng.randint(1,20) for name in old['witnesses']}
        sample.update({'J':J,'F':Fv,'alpha':av,'w':wv})
        ports={'beta':beta,'K0':Kv,'MC':rng.randint(0,30),'MF':rng.randint(0,30)}
        sample.update(ports); oldv=evaluate(old['source'],sample,mod)
        modified={name:sample[name] for name in new['witnesses'] if name!='C'}
        modified.update({'F':Fv-1,'C':Cv+qv,'z':sample['z']+Kv+wv+hv}); modified.update(ports)
        assert all(modified[n]>0 for n in new['witnesses'])
        assert modified['C'] > qv-modified['F']
        newv=evaluate(new['source'],modified,mod)
        if any(oldv[n]!=newv[n] for n in ('gap','R','A0','M','W','Na','Lt','polynomial')):
            raise RuntimeError('transformed graph mismatch')
        samples+=1
result={'status':'PASS_ALGEBRA_AND_SAMPLES_ONLY','graph77_sha256':pins[oldpath],'graph76_sha256':pins[newpath],
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'samples':samples,
        'exact_identities':['gap_invariant','transport_difference','guard_difference'],
        'scope':'Conditional fixed-port transformation; no actual graph zero or Lean theorem produced.'}
out=here/'result.json'; text=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f: f.write(text)
elif sys.argv[1:]: raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=text: raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
