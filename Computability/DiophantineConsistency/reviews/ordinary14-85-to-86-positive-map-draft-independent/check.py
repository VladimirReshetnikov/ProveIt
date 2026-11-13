#!/usr/bin/env python3
"""Independent positive 85/86 map source/finite review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-to-86-positive-map-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'PositiveMap85To86.lean','9f87b9676e4b82db7c622ab6ff4029176e96e0e0ad845a029eb07f4d005c0b56').decode()
pin(A/'check_source.py','5d46deab6d351d73c490b943f4e54e8ee583a984b537d3ec7f0bbdfa47ab10c3')
receipt=pin(A/'observation.json','86eef63ba6492e43453bbf78b952c51cd33ac7c6602ca481ddddf8a96cfeddc2')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-to-86-positive-map-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='87f0f1d703b60a195f380c26bdaccf593f37d62c061c77746790da88c814970e'
pin(D/'research/ordinary14-85-86-ring-client-draft/RingComparison85To86.lean','d8421f203f2f5a973e730771bb6b6d232cc443d31ed67f272e645c205230b353')
g85=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
g86=json.loads(pin(D/'research/ordinary14-residue-guard86/candidate.json','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'))
for f in ('Function.update (Function.update v 7 (q beta v*(q beta v*q beta v)*v 7)) 8 (v 8+v 7)',
 '(hport : (p 0 : DiffRing V)=ι beta) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'forward_positive beta v hv','Ring85To86Draft.output_eval p (fun j => ι (v j))',
 'rw [←cast_forward p beta v hport] at h','rw [h]'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-85-86-ring-client-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
def calc(g,v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(8586021);zero_beta=0
for i in range(600):
 v={n:rng.randrange(1,8) for n in g85['witnesses']};v.update({n:rng.randrange(0,8) for n in g85['fixed_numerals']})
 if i%7==0:v['beta']=0
 q=1+v['J']*v['beta'];w={n:v[n] for n in g86['witnesses'] if n!='Y'}
 w.update({n:v[n] for n in g86['fixed_numerals']});w['Y']=q**3*v['s'];w['r']=v['r']+v['s']
 assert all(w[n]>0 for n in g86['witnesses'])
 assert calc(g85,v)['guarded_out']==calc(g86,w)['guarded_out']
 zero_beta+=v['beta']==0
assert zero_beta
print(json.dumps({'scope':'source and finite positive-map controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'map_controls':600,'beta_zero_controls':zero_beta},sort_keys=True,indent=2))
