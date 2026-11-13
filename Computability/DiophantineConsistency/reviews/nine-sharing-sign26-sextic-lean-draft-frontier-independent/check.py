#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-sextic-lean-draft';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'generate.py':'e2711fe6eb3ca5e21d24c8128bed961bf6f9be03d58df7a8f09743eef51f7219','check.py':'89bb926cde372e4ca1efbf50c85f8d8e96ca781ddc43325cfacee6a27be32307','check_bridge.py':'d2f9d4d717b860cf9e6992c418adcb97ba422efe5bb6169e2294743ed24b508d','SharingSeed26Sextic.lean':'f2614a350eb1b6777bf9acc5723824ddb9362cebd23da6f80ae9e8c5860e5751','SharingSeed26BridgeDraft.lean':'e868506309fc08e1bf62ab19c9a127e04c07b379bb98b941f37f6ff1a83e1beb'}.items():assert H(P/n)==h
for n,status in [('check.py','PASS_SOURCE_AST_TRANSCRIPTION_ONLY'),('check_bridge.py','PASS_SOURCE_MAPPING_ONLY')]:
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/n)],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']==status
s=(P/'SharingSeed26BridgeDraft.lean').read_text();blocks=re.findall(r'!\[([^\]]+)\]',s);assert len(blocks)==2;lift=[x.strip() for x in blocks[0].split(',')];drop=[x.strip() for x in blocks[1].split(',')];assert lift==[f'v {i}' for i in range(22)]+['gap']+[f'v {i}' for i in range(22,27)] and drop==[f'v {i}' for i in range(22)]+[f'v {i}' for i in range(23,28)]
for x in ['let a := ((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)','a * (a + 1) + (ι (v 3) + 1) - a * (ι (v 2) + 1)','((p 0 : ℤ) : DiffRing V) = ι beta','((p 1 : ℤ) : DiffRing V) = ι K','1 ≤ beta','∃ gap : V, ι gap = ringGap p v ∧ InternalZero','def ForwardTarget','def BackwardTarget']:assert x in s
assert not re.search(r'(?m)^\s*(?:theorem|lemma)\b|\b(?:sorry|admit)\b',s)
print(json.dumps({'status':'PASS_SOURCE_DRAFT_REVIEW','scope':'17-row AST parser plus explicit lift/drop and open conditional targets; no Lean elaboration, model positivity, representation or zero bridge'},sort_keys=True,indent=2))
