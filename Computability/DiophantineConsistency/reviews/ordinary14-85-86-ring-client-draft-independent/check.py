#!/usr/bin/env python3
"""Independent 85/86 ring-field source/finite review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-86-ring-client-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'RingComparison85To86.lean','d8421f203f2f5a973e730771bb6b6d232cc443d31ed67f272e645c205230b353').decode()
pin(A/'check_source.py','9a45f51728a77e675f13df4a6ec13f45889c5a679f8bfc6af7c6c8d1c42ab5ef')
receipt=pin(A/'observation.json','b8f2e132daf72b1d49a53521d8564d328b0543d36ba0536ba0a5b1027cc6162c')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-86-ring-client-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='04e82a001573cacbaa7da0e916c6e5ae4823f0b0ef4139fbe926791b40d8661b'
for path,h in {
 'ordinary14-residue-guard86-lean-draft/P86ResidueGraph.lean':'5b655c426151d999745360c8366f940198fcaa1a8408eb905b6b92285a9dcf42',
 'ordinary14-qcube85-lean-draft/P85QcubeGraph.lean':'46c5ffa3344d70b22ca9bc3c56a7b0ba37ac6603a3f7b38f202f5d84fc44ef9b',
}.items():pin(D/'research'/path,h)
g86=json.loads(pin(D/'research/ordinary14-residue-guard86/candidate.json','ecd34ccc9032fd7f2ef1b767b2182fe4d43aa82389b1a6857832c3dd3891c371'))
g85=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
for f in ('[CommRing R]','Function.update (Function.update v 7',
 '((1+v 0*(p 0 : R))*(1+v 0*(p 0 : R)))*v 7)) 8 (v 8+v 7)',
 '(q*(q*q)*b)*(P-(r+s))+(q*(q*q)*s)*b = (q*(q*q)*b)*(P-r)',
 '(P86ResidueGraph.graph p).A0.evalRing (transform p v)',
 '(P86ResidueGraph.graph p).A1.evalRing (transform p v)',
 '(P86ResidueGraph.graph p).aux.evalRing (transform p v)',
 '(P86ResidueGraph.graph p).gap.evalRing (transform p v)',
 '(P86ResidueGraph.graph p).guardResidual.evalRing (transform p v)',
 '(P86ResidueGraph.graph p).output.evalRing (transform p v)'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-residue-guard86-lean-draft-independent','ordinary14-qcube85-lean-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
def calc(g,v,m):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  out=x+y if op=='+' else x-y if op=='-' else x*y
  z[n]=out if m is None else out%m
 return z
rng=random.Random(858601);cases=0
for m in (None,4,6,9,12):
 for _ in range(120):
  v={n:rng.randrange(-5,6) for n in g85['witnesses']+g85['fixed_numerals']};a=calc(g85,v,m)
  w={n:v[n] for n in g86['witnesses'] if n!='Y'};w.update({n:v[n] for n in g86['fixed_numerals']})
  w['Y']=a['Y'];w['r']=v['r']+v['s'];b=calc(g86,w,m)
  assert all(a[f]==b[f] for f in ('A0','A1','Fa','g72','guard','guarded_out'))
  cases+=1
print(json.dumps({'scope':'source and finite ring controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'ring_cases':cases,
 'composite_moduli':[4,6,9,12]},sort_keys=True,indent=2))
