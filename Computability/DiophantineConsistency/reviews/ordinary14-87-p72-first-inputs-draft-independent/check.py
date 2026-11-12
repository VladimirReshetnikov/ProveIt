#!/usr/bin/env python3
"""Independent 87 source interface review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-p72-first-inputs-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','5ee201dc5e6d4f54e3be810c51b5188746d6f4e1536376212b21d396bef7ed71')
s=pin(A/'P72FirstInputs87.lean','f11226321c4738b2b4c7948fd54066d2dc895930dc23bc63a94a30d47a4fdca0').decode()
pin(A/'check_source.py','dd9800b3c884ecac0c3413e76e4c4a047f2a5cb4aa9e1a0376f4f87bdc90176d')
receipt=pin(A/'observation.json','5fe8901879ac305b367e1e342270ee1dade96532f0297c52b37a53fef3ad91d1')
for f in ['RankWindow87Draft.rank_window p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz', 'FirstIndexModQ487Draft.first_index_mod_q4 p beta K MC MF v', 'have h26 : 26≤R', 'rw [mod_eq_self_of_lt hlt] at hmod']:assert f in s,f
n=0
for q in range(2,30):
 for R in range(40,min(100,q**4-1)):
  assert (R+1)%q**4==R+1;n+=1

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
for name in ['ordinary14-87-first-index-modq4-draft-independent', 'ordinary14-87-rank-window-draft-independent']:
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'87 own-zero source interface review; no Lean','finite_controls':n},sort_keys=True,indent=2))
