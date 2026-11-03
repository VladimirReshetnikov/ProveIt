#!/usr/bin/env python3
"""Inspect displayed-kernel iPRA endpoint statements, providers and receipt without Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-bfs-displayed-ipra';S=P/'BFSDisplayed80IPRA.lean';O=P/'observations/attempt01';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='809bbbac1b99b8cb60c4f147bda6526e8ab2ad49c1ccdd3b376b80ca42d6d024' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='1bd3955c52f803242ecfa6fb614a269063a496a42fe6e63f20548a1668b4e766' and sha(P/'run.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='db97c8d4717c6c0a70f51068c1c72b31e314d00864f5a56ac590e92a28367486'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and not (O/'stderr').read_text()
ths=['standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'];expected='\n'.join(f"'BFSDisplayed80IPRA.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in ths)+'\n';assert (O/'stdout').read_text()==expected
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['BFSDisplayedSlots','DirectBFS80FixedIPRA'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert 'ports beta (BFSDisplayedSlots.displayedKernel r) lo hi =' in s and 'ports beta (DirectBFSSymbolicKernel.paramKernel r) lo hi :=' in s and '(BFSDisplayedSlots.kernel_eq_displayed r).symm' in s
assert 'def displayedPorts : Fin 4 → ℕ := ports betaNat (BFSDisplayedSlots.displayedKernel rho) lowNat highNat' in s
for name in ths:
 block=s.split('theorem '+name+' :',1)[1].split('\ntheorem ',1)[0].split('\n#print ',1)[0];assert 'nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)' in block and 'rw [ports_eq]' in block and 'DirectBFS80FixedIPRA.'+name in block
 assert ('standardTheory ⊢' if name.startswith('standard') else 'referenceTheory ⊢') in block
 assert ('erase (' in block)==name.startswith('reference')
 assert ('mappedNativeRefutation embedding' if 'translated' not in name else '(Semiformula.lMap embedding sourceSentence)ᴺ') in block
sel=Path('/tmp/bfs-printed-slots-qwdduxw9/BFSDisplayedSlots.olean');end=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib/DirectBFS80FixedIPRA.olean');assert sha(sel)==t['pins'][str(sel)]['sha256']=='232a18c1544fa215d694391c3fa9fca75abb3eb1ae202f51c624d5a22147ee66';assert sha(end)==t['pins'][str(end)]['sha256']=='2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703'
print('PASS four parameter-free standard/reference iPRA derivability theorem statements use same shifted graph and displayedPorts; equality transports checked fixed client')
print('Selected slot',sha(sel),'selected coherent BFS endpoint',sha(end),'object',t['output_sha256'])
print('PDF/TeX/JSON/gzip binding and complete new-client producer/package/dynamic ancestry remain external; no Lean replay')
