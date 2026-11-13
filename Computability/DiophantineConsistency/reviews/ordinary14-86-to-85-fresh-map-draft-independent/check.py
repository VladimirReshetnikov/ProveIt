#!/usr/bin/env python3
"""Independent fresh reverse-map source/finite review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-86-to-85-fresh-map-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FreshMap86To85.lean','3f8bb56132c5362630d1d43612a8812b88d2a36e4ba407e3ee93990dababdce7').decode()
pin(A/'check_source.py','634bbd1a57eeab01a89abdbb137e2e84865a89fe37fb5a7efa24f3d890a4c51b')
receipt=pin(A/'observation.json','1162930bb29e6b11e838a297ea5662be29c8f7f379ddb2e55edd1f341defe501')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-86-to-85-fresh-map-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='e879ce46142213cd0d0386bf886b866be3f9cbf7370b77d42c753d4869a68fd6'
for path,h in {
 'ordinary14-86-ownzero-quotient-draft/OwnZeroQuotient86.lean':'432175bbc89d27b0cbffe902ac12c00e143d3e473cb02a42280893dfcb94e9c7',
 'ordinary14-86-fresh-root-draft/FreshRoot86.lean':'6e90ba5c820ffb4c4ab48a78993c9145fc897e23d8d78f2667c9135118ecaa62',
 'ordinary14-85-to-86-positive-map-draft/PositiveMap85To86.lean':'9f87b9676e4b82db7c622ab6ff4029176e96e0e0ad845a029eb07f4d005c0b56',
}.items():pin(D/'research'/path,h)
g86=json.loads(pin(D/'research/ordinary14-residue-guard86/candidate.json','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'))
g85=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
for f in ('Function.update (Function.update v 7 s) 8 (firstP v+tau)',
 '(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P86ResidueGraph.graph p).output v)',
 'OwnZeroQuotient86Draft.quotient_and_root','reverse_positive v s tau hv hs htau',
 'fresh_zero p beta v s tau hport hY hn hz','forward_reverse beta v s tau hY',
 'Ring85To86Draft.output_eval p (fun j => ι (w j))','rw [←h]'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-86-ownzero-quotient-draft-independent','ordinary14-86-fresh-root-draft-independent','ordinary14-85-to-86-positive-map-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
def calc(g,v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
cases=0
for beta in range(1,4):
 for J in range(1,4):
  q=1+J*beta;Q=q**3
  for X in range(1,4):
   for s in range(1,4):
    Y=Q*s;k=2;ell=X*Y*Y*k;P=ell+k;tau=2*X*Y*Y+1
    assert tau*tau==1+ell*P
    for sign in (-1,1):
     v={n:1 for n in g86['witnesses']+g86['fixed_numerals']};v.update(beta=beta,J=J,X=X,Y=Y,r=P+s+sign*tau)
     w={n:v[n] for n in g85['witnesses'] if n!='s'};w.update({n:v[n] for n in g85['fixed_numerals']});w['s']=s;w['r']=P+tau
     z86=calc(g86,v);z85=calc(g85,w);fresh=v.copy();fresh['r']=P+tau+s;zf=calc(g86,fresh)
     assert all(w[n]>0 for n in g85['witnesses']) and z86['A0']==z85['A0']==zf['A0']==0
     assert all(z86[n]==z85[n]==zf[n] for n in ('A1','Fa','g72','guard','guarded_out'))
     assert q**3*w['s']==fresh['Y'] and w['r']+w['s']==fresh['r']
     cases+=1
print(json.dumps({'scope':'source and finite partial transfers only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'partial_cases_both_signs':cases},sort_keys=True,indent=2))
