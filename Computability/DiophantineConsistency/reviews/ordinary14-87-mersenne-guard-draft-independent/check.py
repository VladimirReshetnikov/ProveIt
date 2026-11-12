#!/usr/bin/env python3
"""Independent Mersenne guard composition source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-mersenne-guard-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'MersenneGuard87.lean','4c9ed548f74cd8671cb7f95db90fcdf1369a516c7bf0ee27bc3b1394d7e9f448').decode()
pin(A/'check_source.py','86332ffb47dd8b87930520e99d1a9474194342a9846eae97dd8e97f3b61bbb50')
receipt=pin(A/'observation.json','2ad13390fba20a390ce9802fda655105b164781e763669ff887c8dee7179595d')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-mersenne-guard-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='0ff2f172c8ffc6ddcd92f54dbe1cde47d3f1ccf68dbfeb69f566786922c79290'
dep=pin(D/'research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean','d16c6dca1f5bb5240db5e2b72d6d1895568c9e178c933a68e92f82b6be2be43e').decode()
assert 'theorem mersenne_divides_X (t R q J X : V) (ht : 4≤t)' in dep
assert '(hq : q=(Exp.exp t-1)*J+1) (hX : X=Exp.exp R) (hdiv : q∣3*X) : q∣X' in dep
for f in ('(ht : 4≤t) (hradix : beta=Exp.exp t-1)',
 '(hX : v 6=Exp.exp R)','(h3 : q beta v∣3*v 6)',
 '(hz : InternalZero (P87ShiftedGuard.graph p).output v)',
 'mersenne_divides_X t R _ (v 0) (v 6) ht hq hX h3',
 'Arithmetic.le_of_dvd (hv 6) hd',
 'strict_of_large_X p beta K v hbeta hport hK hv hbound hz'):
 assert f in s,f
n=0
for t in range(4,11):
 for J in range(1,30):
  q=((1<<t)-1)*J+1
  for R in range(0,50):
   X=1<<R
   if (3*X)%q==0:
    assert X%q==0 and q<=X
    n+=1
assert n>0
def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ('ordinary14-87-guard-strict-linear-draft-independent','ordinary14-modified-carrier-model-facts-draft-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'conditional model-source composition; no Lean or recovered calibration',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'finite_divisibility_cases':n},sort_keys=True,indent=2))
