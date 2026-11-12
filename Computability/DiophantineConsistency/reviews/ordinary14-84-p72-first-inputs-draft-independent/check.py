#!/usr/bin/env python3
"""Independent first-input composition source review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-p72-first-inputs-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'P72FirstInputs.lean','66f7552cbc7b89a42e1bd81366313bd1d4ee77aafec29368623fc210b864cab8').decode()
pin(A/'check_source.py','36a0b8831b92e74eee65c3e613b006b894e7d1ba6f5bbfffccd49bb3cc5ececb')
receipt=pin(A/'observation.json','d20df07316964c1fc3131d647aa234e2c40934dd8019f114a07f45978ec98880')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-p72-first-inputs-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='f48ec74e7f68a8baa14e82379a96c9c8ee7fa0efa6f6958dd120420902e70519'
for path,h in {
 'ordinary14-84-first-index-modq4-draft/FirstIndexModQ4.lean':'9e773426457e25dbab91ea1b6aee42f1691fc538de000a57cfd7edf3b9f387f2',
 'ordinary14-84-rank-window-draft/RankWindow.lean':'f0fce525b747e9e053be8752e740ac3171a22f00026cbaa2f14c5ce9cc5f57cb',
 'ordinary14-84-rank-lower40-draft/RankLower40.lean':'0786421d6d1520e21026e15d36c72ffc00d1c14ebf54bc5c4221ba4e81e9cbd1',
}.items():pin(D/'research'/path,h)
for f in ('(hMC : MC<beta) (hMF : MF<2*beta)',
 '(hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v)',
 '26≤R ∧ R+1<q^4','(2*n)%(q^4)=R+1',
 'rank_lower40 p beta K MC MF v hbeta hport hK hv hz',
 'rank_window p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'first_index_mod_q4 p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz',
 'rw [mod_eq_self_of_lt hlt] at hmod'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-first-index-modq4-draft-independent','ordinary14-84-rank-window-draft-independent','ordinary14-84-rank-lower40-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=above=0
for q in range(3,9):
 m=q**4
 for R in range(40,min(m-1,180)):
  assert R+1<m
  for t in range(5):
   x=R+1+t*m
   if x%2:continue
   n=x//2
   assert 26<=R and (2*n)%m==(R+1)%m==R+1
   above+=2*n>=m;cases+=1
assert above
print(json.dumps({'scope':'source and finite modulo controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'modulo_cases':cases,
 'first_index_at_least_modulus':above,'independent_dependency_reviews':3},sort_keys=True,indent=2))
