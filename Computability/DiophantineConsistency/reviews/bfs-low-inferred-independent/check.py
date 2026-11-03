#!/usr/bin/env python3
"""Check inferred low-mask proof type from its two source lemmas and retained receipt; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ten-positive-80-bfs-low-inferred';S=P/'BFSDisplayedLowInferredV4.lean';O=P/'observations/attempt04';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='9b66c35984d3e26cbf7c2219195b7470f66d7375d0b6397720b8cf0864186d11' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='decd50ce604960b0036a18b16d65e70bf2bc13b1d27c875138568d320a5360b5' and sha(P/'run-v4.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='a895ead4d840a0357790745e6093616e07b14129ce8f6259ddd486c87b82da9d'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and (O/'stdout').read_text()=="'BFSDisplayedLowInferred.low_formula' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stderr').read_text()
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['BFSDisplayedBetaIPRAV2'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert s.count('set_option linter.defProp false in')==1 and re.search(r'set_option linter\.defProp false in\s*def low_formula := Eq\.trans low_alias CompactConcreteMask\.concrete_recipe',s)
assert 'theorem low_alias : CompactSymbolicPorts.lowNat =' in s and 'Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support) := rfl' in s
C=R/'ordinary12-ipra-bridge/compact44-concrete-mask-prototype/CompactConcreteMask.lean';c=C.read_text();assert re.search(r'theorem concrete_recipe\s*:\s*Nat\.ofDigits \(2\^67\) \(digits \(2\^67\) 8807 1063 support\)\s*=\s*\(2\^67\)\^8807 - 1 - \(∑ j ∈ support, \(2\^67\)\^j\) - 2\*\(2\^67\)\^1063',c)
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in c and '{1063,1064,1095,2195,3296}) \\ {1}' in c
q=R/'ordinary12-ipra-bridge/compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean';assert 'def lowNat : ℕ := Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)' in q.read_text()
prov=Path('/tmp/bfs-printed-beta-sjarp8v0/BFSDisplayedBetaIPRAV2.olean');assert sha(prov)==t['pins'][str(prov)]['sha256']=='b82dd329e8e0ac45932e9debd5ccae15b5c3133c1b9ce270891363a335624bd8'
for i in (1,2,3):
 b=P/f'observations/attempt{i:02}';z=json.loads((b/'terminal.json').read_text());assert z['status']=='FAILED' and sha(b/'stdout')==z['stdout_sha256'] and sha(b/'stderr')==z['stderr_sha256'];log=(b/'stdout').read_text()+(b/'stderr').read_text()
 if i==2:assert z['exit']==0 and 'warning:' in log and 'linter.defProp' in log
 else:assert z['exit']!=0 and re.search(r'error(?:\([^\n:]*\))?:',log)
print('PASS inferred Eq.trans type lowNat = (2^67)^8807−1−Σ_support(2^67)^j−2*(2^67)^1063; direct provider pin, local linter suppression, 3 rejected attempts')
print('Source-level inference only; no #print type transcript, no formal PDF/file or displayed-port join, no Lean replay.')
