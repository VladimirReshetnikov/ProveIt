#!/usr/bin/env python3
import hashlib,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-octic-lean-draft';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'generate.py':'771c941596214bc3a908661ab908d332825f0c95f55a86cbde6a4035b7f28711','check.py':'4da1db6fcb4e693441f9aa5bc4221b6356a96bd4fa1fa0582808cac0d8a2d5b6','check_bridge.py':'1e9c51bc85b78fa49238b157038007b184935990569c5fc51d3d8dc0e9d36809','SharingSeed25Octic.lean':'25f4c55e4f9587db295d4fe95908ef6866202c9690204b9dfa88c27b7ea547ec','SharingSeed25BridgeDraft.lean':'62a6a45b6b1aa669282da1823d2757aa031dae02767159d966da989de702faa1'}.items():assert H(P/n)==h
S=D/'research/nine-sharing-sign25-octic-ell-candidate/seed.json';assert H(S)=='c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8';rows=json.loads(S.read_text())['residuals'];s=(P/'SharingSeed25Octic.lean').read_text();first=s.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 26) :=\n  ',1)[1].split('\n',1)[0];block=s.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 26)) :=\n  [\n',1)[1].split('\n  ]',1)[0];lines=[first]+[x.strip().removesuffix(',') for x in block.splitlines()];assert len(lines)==len(rows)==16
# Independently serialize external trees bottom-up, then compare each Lean term.
def render(t):
 todo=[(t,False)];stack=[];ports={'beta':0,'K0':1,'MC':2,'MF':3};sym={'add':'+','sub':'-','mul':'*'}
 while todo:
  a,done=todo.pop();op=a[0]
  if op=='var':assert 1<=a[1]<=25;stack.append(f'(Expr.var {a[1]})')
  elif op=='num':stack.append(f'(Expr.constant ({a[1]} : ℤ))')
  elif op=='port':stack.append(f'(Expr.constant (p {ports[a[1]]}))')
  elif not done:assert op in sym and len(a)==3;todo.extend([(a,True),(a[2],False),(a[1],False)])
  else:
   right=stack.pop();left=stack.pop();stack.append(f'({left} {sym[op]} {right})')
 assert len(stack)==1;return stack[0]
assert [render(x['expr']) for x in rows]==lines and 'set_option maxHeartbeats 4000000' in s and 'firstResidual p * firstResidual p +' in s and 'QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)' in s
bridge=(P/'SharingSeed25BridgeDraft.lean').read_text();blocks=re.findall(r'!\[([^\]]+)\]',bridge);assert len(blocks)==2;lift=[x.strip() for x in blocks[0].split(',')];drop=[x.strip() for x in blocks[1].split(',')];assert lift==[f'v {i}' for i in range(19)]+['v 17 * v 18']+[f'v {i}' for i in range(19,26)] and drop==[f'v {i}' for i in range(19)]+[f'v {i}' for i in range(20,27)];assert all(x in bridge for x in ['def ForwardTarget','def BackwardTarget','InternalZero (SharingSeed25Octic.seed p) v','InternalZero (SharingSeed26Sextic.seed p) (lift v)','InternalZero (SharingSeed26Sextic.seed p) v','InternalZero (SharingSeed25Octic.seed p) (drop v)']) and not re.search(r'(?m)^\s*(?:theorem|lemma)\b|\b(?:sorry|admit)\b',bridge)
for n,record,status in [('check.py','result.json','PASS_SOURCE_AST_TRANSCRIPTION_ONLY'),('check_bridge.py','bridge-result.json','PASS_SOURCE_MAPPING_ONLY')]:
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/n)],capture_output=True,text=True,check=True,timeout=120);assert json.loads(r.stdout)==json.loads((P/record).read_text()) and json.loads(r.stdout)['status']==status
with tempfile.TemporaryDirectory(prefix='sign25-source-audit-',dir=D/'research') as t:
 t=Path(t);shutil.copyfile(P/'generate.py',t/'generate.py');r=subprocess.run([sys.executable,'-I','-S','-B',str(t/'generate.py')],check=True,capture_output=True,text=True,timeout=120);assert (t/'SharingSeed25Octic.lean').read_bytes()==(P/'SharingSeed25Octic.lean').read_bytes() and json.loads(r.stdout)==json.loads((P/'generation-result.json').read_text())
up=D/'reviews/nine-sharing-sign25-octic-ell-frontier-independent/check.py';assert H(up)=='f4e5cd25205b4f0afa601d2a6fb68d09d0b86aabbcf803711810bae0ad828ca3';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_SOURCE_DRAFT_REVIEW','scope':'16 external ASTs, generator reproduction, Fin26↔Fin27 lift/drop and open targets; no Lean elaboration, zero bridge or endpoint','heartbeat_option':4000000},sort_keys=True,indent=2))
