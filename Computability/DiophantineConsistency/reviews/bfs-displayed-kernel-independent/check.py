#!/usr/bin/env python3
"""Inspect accepted symbolic BFS kernel recipe and retained failures; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-bfs-selectors-lean';S=P/'BFSDisplayedKernelV4.lean';O=P/'observations/kernel-attempt04';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='df0cbaa918a95c0b45b6ee552e248efaefb494ccbe3964787c1b9b8c8fe05b8c' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='18060922ec3a1587334806fbd7442e1cca2d00b806d423fb18f840aa1d3517bb' and sha(P/'run-kernel-v4.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='bd6b509d78529c1c9879774a11989d605849c282ba4d408ef1ecfe1ed36bc072'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and (O/'stdout').read_text()=="'BFSDisplayedKernel.kernel_eq_displayed' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stderr').read_text()
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['BFSDisplayedSelectors'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert re.search(r'theorem kernel_eq_displayed \(r : ℕ\) :\s*DirectBFSSymbolicKernel.paramKernel r = displayedKernel r',s)
assert '∑ i : Fin 943, displayedSelector i' in s and '∑ i : Fin 41' in s and '(4393-position i)' in s and '(5495-position i)' in s and 'r^8849' in s
assert 'BFSDisplayedSelectors.values_eq_rows_map' in s and 'Nat.pow_add r 8807 42' in s
prov=Path('/tmp/bfs-printed-selectors-4w6qxofm/BFSDisplayedSelectors.olean');kernel=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib/DirectBFSSymbolicKernel.olean');assert sha(prov)==t['pins'][str(prov)]['sha256']=='92f60899906162de5e0ff953b4f9f0041f7471d17ee65e31a90db33b6363c65f';assert sha(kernel)==t['pins'][str(kernel)]['sha256']=='69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f'
for i in range(1,4):
 o=P/f'observations/kernel-attempt{i:02}';z=json.loads((o/'terminal.json').read_text());assert z['status']=='FAILED' and sha(o/'stdout')==z['stdout_sha256'] and sha(o/'stderr')==z['stderr_sha256'];log=(o/'stdout').read_text()+(o/'stderr').read_text()
 if i<3:assert z['exit']!=0 and 'error:' in log and 'sorryAx' in log
 else:assert z['exit']==0 and log.count('warning:')==2
v3=(P/'BFSDisplayedKernelV3.lean').read_text();assert v3.replace('set_option maxHeartbeats 20000000\n','set_option maxHeartbeats 20000000\nset_option exponentiation.threshold 9000\n',1).replace('  simpa only [List.get_eq_getElem, BFSDisplayedSelectors.values_eq_rows_map, List.getElem_map]','  simp only [List.get_eq_getElem, BFSDisplayedSelectors.values_eq_rows_map, List.getElem_map]',1)==s
print('PASS arbitrary-r Lean kernel recipe with explicit 943 selectors and symbolic 41 positions, accepted object/pins and three retained rejected attempts')
print('No Lean PDF parsing, explicit position equality, coefficient-byte binding or independent Lean replay.')
