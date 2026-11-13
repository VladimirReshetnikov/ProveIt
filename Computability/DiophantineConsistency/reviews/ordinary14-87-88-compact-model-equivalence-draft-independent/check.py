#!/usr/bin/env python3
"""Independent compact 87↔88 source wrapper review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-88-compact-model-equivalence-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return b
pin(A/'README.md','217d193740895f5fcaaaf31d8bd1c6d6c659d17d31eda7819b403befebd80154')
s=pin(A/'CompactEquivalence8788.lean','144941561caad5cb1dbf3dc0edab48ed81ab944d3af7dddde2ff3eff50add152').decode()
pin(A/'check_source.py','25bb8d78a361e50edc686984d0c1459fd2f1155dd92645a91574d933d39cbfa2')
receipt=pin(A/'observation.json','df5636905e0d9b8b4edb88f126681fe175b2d1eaeb7ff00a8cadeddcbb27ef0b')
p=D/'reviews/ordinary14-87-88-model-equivalence-draft-independent'
pin(p/'check.py','3b6ca38d3b432b9da51114d2b7bdc5685a3b96eca2da802db198c2e5cbb046e9')
pin(p/'result.json','a56cf0a029d82504eed104424ca82111794852ddaed05ff3dd2c01190a6bc5f3')
ports=pin(D/'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414').decode()
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
for f in ('theorem positive_zero_iff (K : ℕ)','ports CompactFixedBeta.betaNat K lowNat highNat',
 'C44Short15Facts.port_bounds','P72Root.cast_port p 0','P72Root.cast_port p 1',
 'P72Root.cast_port p 2','P72Root.cast_port p 3',
 '(p 3 : V) hb.1 hb.2.2.2','hp0 hp1 hp2 hp3 hb.2.1 hb.2.2.1'):
 assert f in s,f
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'compact 87/88 symbolic source wrapper review; no Lean','prior_generic_review':'pinned, not rerun'},sort_keys=True,indent=2))
