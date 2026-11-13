#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-78-74-model-composition-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'600a6165b878fa412afeda97c4c98ecf07ddc50cc229b89061bd5164aaa79602',A/'Model78To74.lean':'dd18b7795ed5c9e9bfa4bd9f1d78aa134b4a896c80ed1f4e24478a0add220b76',A/'check_source.py':'64c0ca7a8362fd9c13876918468f40c9202fafd924a20f6b07fac08c2429d1e5',A/'observation.json':'dc3bce5bf431905aaa64f0bf5211c63260a1a2322f6bf28ecee33764b0cc15dc',D/'research/ordinary14-78-75-model-equivalence-draft/ModelEquivalence78To75.lean':'482a6102d4e339d3997a5208fc7ee1becacc5beecaf05f4f06e4a11b5b683f6c',D/'research/ordinary14-75-74-model-discrete-draft/ModelDiscrete75To74.lean':'2154e4c72f347b48ace2b73e98782b64d87e274c8f4b2b2b6379de054ad4f404',D/'research/ordinary14-75-74-model-equivalence-draft/ModelEquivalence75To74.lean':'d0b87479f1370ee5c1d9510a94258fabd333f8b64d01e479aa66230a1c3c42ac',D/'research/ordinary14-75-74-positive-map-draft/Positive75To74.lean':'c8e10e66643f025988751af1a55b7d70dc23ea25eec70b6efe4dc256003b7d70'}
tail=b'\nIndependent source review: [78 to 74 model composition](../../reviews/ordinary14-78-74-model-composition-independent/README.md).\n'
readme=(A/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()=='f6e543ed77b643a25426789df2ee87d010d939dab082e1fc527f25480fb01a2c'
assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()==pins[A/'README.md']
for p,h in pins.items():
 if p!=A/'README.md':assert sha(p)==h,(str(p),sha(p))
s=(A/'Model78To74.lean').read_text();point=(D/'research/ordinary14-78-75-model-equivalence-draft/ModelEquivalence78To75.lean').read_text();mid=(D/'research/ordinary14-75-74-model-discrete-draft/ModelDiscrete75To74.lean').read_text();maps=(D/'research/ordinary14-75-74-positive-map-draft/Positive75To74.lean').read_text()
for t in ('(p : Fin 4 → ℕ) (hb : 0<(p 0 : V))','ModelEquivalence7875Draft.zero_iff_natural_ports p v hb hv).mpr hz','ModelEquivalence7875Draft.zero_iff_natural_ports p v hb hv).mp hz','hfirst.trans (ModelDiscrete7574Draft.positive_zero_iff_natural_ports p hb)'):
 assert t in s,t
for t in ('InternalZero (P75NegativePell.graph (fun j => (p j : ℤ))).output v ↔','InternalZero (P78AuxRoot.graph (fun j => (p j : ℤ))).output v','(hb : 0<(p 0 : V)) (hv : ∀ j, 0<v j)'):
 assert t in point,t
for t in ('InternalZero (P75NegativePell.graph (fun j => (p j : ℤ))).output v','InternalZero (P74PositiveGuard.graph (fun j => (p j : ℤ))).output v','ModelEquivalence7574Draft.positive_zero_iff_natural_ports p difference_ring_discrete hb'):
 assert t in mid,t
assert 'Function.update v 13 (v 13+1)' in maps and 'Function.update v 13 (v 13-1)' in maps
# Schematic witness-direction controls: choose arbitrary subsets of positive
# 75 valuations h=1..4 and transfer to h+1; the reverse uses h-1 only on
# shifted witnesses. This is not a literal graph-zero search.
cases=0
for mask in range(16):
 S={h for h in range(1,5) if mask & (1<<(h-1))}
 T={h+1 for h in S}
 assert bool(S)==bool(T)
 for h in S:assert h+1 in T and h+1>1
 for h in T:assert h-1 in S and h-1>0
 cases+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert rr.stdout==(A/'observation.json').read_bytes() and not rr.stderr
print(json.dumps({'scope':'source-interface and schematic iff/witness controls; no Lean or actual graph-zero claim','schematic_witness_sets':cases,'author_receipt_replayed':True,'reviewed_readme_sha256':pins[A/'README.md']},sort_keys=True,indent=2))
