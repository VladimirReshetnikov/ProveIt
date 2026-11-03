#!/usr/bin/env python3
"""Audit generic high-digit run identities, not fixed mask; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-bfs-high-generic';S=P/'BFSHighGeneric.lean';O=P/'observations/attempt01';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='7c9a936b8f36af025d30f9f386100f8d0692ab448f32afd2d69bd51eaf345d88' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='8b0fa6e1f6dc150ea1faee57e1b2beb8453a31c1bf2adbb6e1775efb3b5a1225' and sha(P/'run.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='cdb9593b8e095fbe92ecc3d89fef9e7c77c4a98a3b1688b4988d6d48bc7cc1ff'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and not (O/'stderr').read_text();expected='\n'.join(f"'BFSHighGeneric.{x}' depends on axioms: [propext, Classical.choice, Quot.sound]" for x in ('replicate_value','run_sum'))+'\n';assert (O/'stdout').read_text()==expected
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['DiophantineConsistency.CompactConcreteMask','DiophantineConsistency.CompactHighPopulation'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert 'theorem replicate_value (B n d : ℕ)' in s and 'Nat.ofDigits B (List.replicate n d) = d * (∑ j ∈ range n, B^j)' in s and 'theorem run_sum (B n d : ℕ) (xs : List ℕ)' in s and 'd * (∑ j ∈ range n, B^j) + B^n * Nat.ofDigits B xs' in s
for n in ('CompactConcreteMask','CompactHighPopulation'):
 p=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib/DiophantineConsistency')/(n+'.olean');assert sha(p)==t['pins'][str(p)]['sha256'];print(n,p,p.resolve(),sha(p))
print('PASS two generic Nat.ofDigits run identities, no fixed high-mask equality or Lean replay')
