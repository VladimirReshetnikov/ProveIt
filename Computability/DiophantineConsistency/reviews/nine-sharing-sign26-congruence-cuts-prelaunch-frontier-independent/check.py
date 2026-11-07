#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-congruence-cuts-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'f6ae0b666d86966930d5b74060ca16da1e17765c75c7c92b509af1e3514fe885','source-manifest.json':'4ba45b273f5b91c8bbb763b5ebe943c37aefd09cac1627f67c24228c3961f0fd','sign27-survey.py':'5dfe8c0712086c4a37390e90d7392a1e2cc735280e2f3ad4e76f5942e34ec218','src/DiophantineConsistency/Sign26CongruenceCuts.lean':'c239bc0e18ba69ef8683a2e33c18278f80b87a0813caefa29592a30126e934f0'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign26ZeroExtraction','DiophantineConsistency.SharingSign27Squares'];s=(P/'src/DiophantineConsistency/Sign26CongruenceCuts.lean').read_text();assert H(D/'research/nine-sharing-sign26-congruence-cuts-draft/Sign26CongruenceCuts.lean')==m[0]['source_sha256']
draft=(D/'research/nine-sharing-sign26-sextic-lean-draft/SharingSeed26BridgeDraft.lean').read_text()
for name in ['lift','ringGap']:
 assert s.split(f'def {name} ',1)[1].split('\n\n',1)[0]==draft.split(f'def {name} ',1)[1].split('\n\n',1)[0]
rows={}
for n in (27,26):
 t=(D/f'research/nine-sharing-sign{n}-sextic-lean-draft/SharingSeed{n}Sextic.lean').read_text().split('def remainingResiduals ',1)[1].split('\n  [\n',1)[1].split('\n  ]',1)[0];rows[n]=[x.strip().removesuffix(',') for x in t.splitlines()]
for label,oldidx,newidx in [('Gap',7,None),('Tau',8,7),('Inner',11,10)]:
 for tag,n,idx in [('old',27,oldidx),('new',26,newidx)]:
  if idx is None:continue
  expr=s.split(f'def {tag}{label} ',1)[1].split(':=\n',1)[1].split('\n',1)[0].strip();assert expr==rows[n][idx];assert f'((SharingSeed{n}Sextic.remainingResiduals p).drop {idx}).head? = some ({tag}{label} p)' in s
for label in ['Tau','Inner']:
 t=s.split(f'theorem {label}_eval ',1)[1].split(':= by',1)[0];assert '(hgap : ι gap = ringGap p v)' in t and '(hq3 : ι (v 15) =' in t
assert '(hgap : ι gap = ringGap p v)' in s.split('theorem oldGap_zero ',1)[1].split(':= by',1)[0]
up=D/'reviews/nine-sharing-sign26-zero-extraction-terminal-frontier-independent/check.py';assert H(up)=='bad783a7578e21edbcffb029ffc809131be27d72a32609ef590a48849640dade';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'old gap zero with represented gap; first row; Tau/Inner identities require both hgap and q3; no assembled bridge or Lean replay'},sort_keys=True,indent=2))
