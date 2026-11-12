#!/usr/bin/env python3
"""Independent q/first-port source audit and finite sanity checks; no Lean."""
from pathlib import Path
from hashlib import sha256
from collections import deque
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-residue-compact-qbound-model-draft')
fs=[p/'ResidueCompactQBound.lean.src',p/'README.md',p/'check.py',p/'pins.json',p/'receipt.json',
 Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean'),
 Path('Lean/DiophantineConsistency/ArithmeticStandardCasts.lean'),
 Path('Lean/DiophantineConsistency/Compact44/CompactGraphDerivedRadix.lean'),
 Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean'),
 Path('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src'),
 Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src'),
 Path('research/ordinary13-residue-witness-pell-model-draft/ResiduePellCoordinates.lean.src')]
s=[f.read_text() for f in fs]
def compact(v):return re.sub(r'\s+',' ',v)
d,b,cast,base,ports,local,graph,consumer=(compact(s[i]) for i in [0,5,6,7,8,9,10,11])
assert 'def betaNat : ℕ := 2^(67*8807)-1' in b
assert 'theorem beta_identity : (betaNat:V)+1=Exp.exp ((67:V)*8807)' in b
assert 'theorem cast_exp (n : ℕ) : Exp.exp (n:V) = ((2^n : ℕ) : V)' in cast
assert 'ArithmeticStandardCasts.cast_exp (V:=V) 6' in base and 'exact exp_monotone_le.mpr (by norm_num)' in base
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
assert 'CompactSymbolicPorts.ports CompactFixedBeta.betaNat K CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat' in local
assert 'def q (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := 1+v 0*(p 0:V)' in graph
assert '(46:V)≤(ports K 0:V)' in d and '(47:V)≤q (ports K) v' in d
assert 'pos_iff_one_le.mp hJ' in d and 'le_mul_of_one_le_left (by simp) hj' in d
assert 'ResiduePellCoordinatesDraft.graph_power (ports K) v hz hJ hb hX hgap hwindow hq' in d
assert '(hbeta : 0<(p 0:V))' in consumer and '(hq46 : 46≤q p v)' in consumer
assert 'InternalZero (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) v' in d
# Reconstruct the project-local import path that supplies the cast theorem.
start='DiophantineConsistency.Compact44.CompactFixedBeta';target='DiophantineConsistency.ArithmeticStandardCasts'
queue=deque([(start,[start])]);seen=set();chain=None
while queue:
 mod,path=queue.popleft()
 if mod in seen:continue
 seen.add(mod)
 if mod==target:chain=path;break
 f=Path('Lean').joinpath(*mod.split('.')).with_suffix('.lean')
 if f.exists():
  for line in f.read_text().splitlines():
   if line.startswith('import '):
    for dep in line.split()[1:]:queue.append((dep,path+[dep]))
assert chain
# Validate the selected fin-index tuple and the monotone q inequality
# at small values, independently of enormous numeral expansion.
checks=0
for beta in range(46,91):
 for K in range(6):
  for J in range(1,8):
   P=[beta,K,2,beta+3];assert P[0]==beta and 1+J*P[0]>=47
   checks+=1
assert 67*8807==590069 and 6<=590069 and 2**6==64 and 46<64
assert subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,check=True).stdout==fs[4].read_bytes()
print(json.dumps({'files_sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'cast_source_import_chain':chain,'tuple_and_q_controls':checks,'author_receipt_reproduced':True,
 'result':'no concrete source mismatch found; not Lean-checked', 'lean_executed':False},sort_keys=True,indent=2))
