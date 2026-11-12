#!/usr/bin/env python3
"""Independent direct 85 first-input source review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-p72-first-inputs-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'P72FirstInputs85.lean','21bc4a16c39fe004912d4122325fffc1291fe55e9c5926281700663c6794e0bb').decode()
pin(A/'check_source.py','1a32292ce57541829fbffd5ffeb5f8c78ff1c00ae6f43b933a62ffec68eb9868')
receipt=pin(A/'observation.json','dd678d7d5e2f3e0768bcd2fb760a86c06964f3447b9e949717af5851603f5d52')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-p72-first-inputs-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='cc7772846b7b4b7a327e64fc2e3fa82381a5b3bae08704c5ba76e798dd0c1694'
for path,h in {
 'ordinary14-85-first-index-modq4-draft/FirstIndexModQ485.lean':'c0374006dcd0a93a991dd7cf3551f902656fdd7750cc92abfcd7abc3cf23b2a7',
 'ordinary14-85-rank-window-draft/RankWindow85.lean':'abd05c05b598b5e0c9f0ead37993e4f38a4a409304c050f1b4f1a3ef9cb6f30d',
}.items():pin(D/'research'/path,h)
for f in ('(hMC : MC<beta) (hMF : MF<2*beta)',
 '(hv : ∀ j, 0<v j) (hz : InternalZero (P85QcubeGraph.graph p).output v)',
 '26≤R ∧ R+1<q^4','(2*n)%(q^4)=R+1',
 'RankWindow85Draft.rank_window p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'FirstIndexModQ485Draft.first_index_mod_q4 p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz',
 'rw [mod_eq_self_of_lt hlt] at hmod'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-85-first-index-modq4-draft-independent','ordinary14-85-rank-window-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=above=0
for q in range(3,9):
 m=q**4
 for R in range(40,min(m-1,180)):
  for t in range(5):
   x=R+1+t*m
   if x%2:continue
   n=x//2
   assert 26<=R and R+1<m and (2*n)%m==R+1
   above+=2*n>=m;cases+=1
assert above
print(json.dumps({'scope':'source and finite modulo controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'modulo_cases':cases,
 'first_index_at_least_modulus':above},sort_keys=True,indent=2))
