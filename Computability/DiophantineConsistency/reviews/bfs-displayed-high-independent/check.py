#!/usr/bin/env python3
"""Review arbitrary-radix high recipe and displayed high iPRA endpoint; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];R=D/'research'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
cases=[('ten-positive-80-bfs-high-symbolic','BFSHighSymbolic','14ab36e57e6db61a4a11036e95a05afa44b7cec31b01440b9db02c214a38cbf5','22bcd8ea4301cb1141db3b51bf6ba08a664561cb6d670e551ee3d0c165daa841','be648d1039d9fa37de74883e13619b17df735e5693f6b7e7174b42922f312c9c',['BFSHighFlat'],['high_recipe']),('ten-positive-80-bfs-displayed-high','BFSDisplayedHighIPRA','5238a57003cc539868f5527617dbd8c67f286ecc654c20a55d9a47463cfd1c40','1bd9030818a307fa0bcd964da013877534c2e5b300aeca85c174e80beddef077','2cfc21175d514752d6f303b216c58890f455fd5f98687c777a5ea74c30a198bb',['BFSDisplayedBetaIPRAV2','BFSHighSymbolic'],['standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'])]
for folder,mod,termhash,srcsha,objsha,imports,names in cases:
 P=R/folder;S=P/(mod+'.lean');O=P/'observations/attempt01';t=json.loads((O/'terminal.json').read_text());assert sha(O/'terminal.json')==termhash and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
 assert sha(S)==t['source_sha256']==srcsha and sha(P/'run.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']==objsha
 for p,z in t['pins'].items():assert sha(p)==z['sha256'] and str(Path(p).resolve())==z['resolved'],p
 assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and not (O/'stderr').read_text();expected='\n'.join(f"'{mod}.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)+'\n';assert (O/'stdout').read_text()==expected
 s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==imports and not re.search(r'\b(?:sorry|admit)\b',s)
 if mod=='BFSHighSymbolic':
  assert 'theorem high_recipe (B : ℕ) : Nat.ofDigits B highDigits = displayedHigh B' in s and 'BFSHighFlat.expansion B mu padding lastPadding' in s
  for frag in ['Ico 1013 1023','Ico 1065 1074','Ico 8792 8805','B^2195 + B^3296','mu*(B^4393+B^5495)','lastPadding*B^8805']:assert frag in s
 else:
  assert 'theorem high_eq : BFSHighSymbolic.displayedHigh rho = highNat' in s and 'ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho) lowNat (BFSHighSymbolic.displayedHigh rho)' in s and '(fun hi => ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho) lowNat hi) high_eq' in s
  for n in names:
   block=s.split('theorem '+n+' :',1)[1].split('\ntheorem ',1)[0].split('\n#print ',1)[0];assert 'nativeNoZero (positiveShift (graph (integerPorts displayedPorts)).output)' in block and 'rw [ports_eq]' in block and 'BFSDisplayedBetaIPRA.'+n in block
   assert ('standardTheory ⊢' if n.startswith('standard') else 'referenceTheory ⊢') in block and (('erase (' in block)==n.startswith('reference'))
   assert ('mappedNativeRefutation embedding' if 'translated' not in n else '(Semiformula.lMap embedding sourceSentence)ᴺ') in block
 print(mod,'output',objsha,'direct',imports)
H=R/'ordinary12-ipra-bridge/compact44-high-population-prototype/CompactHighPopulation.lean';h=H.read_text();assert 'def mu : ℕ := 2^51-2' in h and 'def padding : ℕ := 2^65-1' in h and 'def lastPadding : ℕ := 2^19-1' in h
ports=(R/'ordinary12-ipra-bridge/compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean').read_text();assert 'def highNat : ℕ := Nat.ofDigits (2^67) CompactHighPopulation.highDigits' in ports and 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
print('PASS arbitrary-radix high recipe and four no-premise shifted-graph iPRA forms; high adds beta once, lowNat stays symbolic; no Lean replay')
