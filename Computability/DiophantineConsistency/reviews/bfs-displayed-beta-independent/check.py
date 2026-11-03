#!/usr/bin/env python3
"""Inspect displayed beta iPRA endpoint statements, providers and receipt without Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-bfs-displayed-beta';S=P/'BFSDisplayedBetaIPRAV2.lean';O=P/'observations/attempt02';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='a08e139f5e597fe4d09b036ed035ba8b6df68385b20b4f21205c3e3b8b405d9c' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='6ff15578cdb558cc073eed14b117522164eaaa3ebe05a47ca07e3a70f029dc92' and sha(P/'run-v2.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='b82dd329e8e0ac45932e9debd5ccae15b5c3133c1b9ce270891363a335624bd8'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and not (O/'stderr').read_text()
ths=['standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'];expected='\n'.join(f"'BFSDisplayedBetaIPRA.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in ths)+'\n';assert (O/'stdout').read_text()==expected
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['BFSDisplayed80IPRA'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert 'def displayedBeta : ℕ := ((2:ℕ)^67)^8807 - 1' in s and 'theorem beta_generic (a m n : ℕ) : (a^m)^n - 1 = a^(m*n) - 1' in s
assert 'theorem beta_eq : displayedBeta = CompactFixedBeta.betaNat' in s and 'exact beta_generic 2 67 8807' in s
assert 'ports displayedBeta (BFSDisplayedSlots.displayedKernel rho) lowNat highNat' in s and 'congrArg (fun beta => ports beta (BFSDisplayedSlots.displayedKernel rho) lowNat highNat) beta_eq' in s
for name in ths:
 block=s.split('theorem '+name+' :',1)[1].split('\ntheorem ',1)[0].split('\n#print ',1)[0];assert 'nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)' in block and 'rw [ports_eq]' in block and 'BFSDisplayed80IPRA.'+name in block
 assert ('standardTheory ⊢' if name.startswith('standard') else 'referenceTheory ⊢') in block
 assert ('erase (' in block)==name.startswith('reference')
 assert ('mappedNativeRefutation embedding' if 'translated' not in name else '(Semiformula.lMap embedding sourceSentence)ᴺ') in block
sel=Path('/tmp/bfs-printed-ipra-9m_nfq32/BFSDisplayed80IPRA.olean');end=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib/DirectBFS80FixedIPRA.olean');assert sha(sel)==t['pins'][str(sel)]['sha256']=='db97c8d4717c6c0a70f51068c1c72b31e314d00864f5a56ac590e92a28367486';assert sha(end)==t['pins'][str(end)]['sha256']=='2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703'
bad=P/'observations/attempt01';z=json.loads((bad/'terminal.json').read_text());log=(bad/'stdout').read_text()+(bad/'stderr').read_text();assert z['status']=='FAILED' and z['exit']!=0 and 'maximum recursion depth' in log and 'sorryAx' in log
print('PASS four parameter-free standard/reference iPRA derivability theorem statements use same shifted graph and displayedPorts; equality transports checked fixed client')
print('Selected slot',sha(sel),'selected coherent BFS endpoint',sha(end),'object',t['output_sha256'])
print('PDF/TeX/JSON/gzip binding and complete new-client producer/package/dynamic ancestry remain external; no Lean replay')
