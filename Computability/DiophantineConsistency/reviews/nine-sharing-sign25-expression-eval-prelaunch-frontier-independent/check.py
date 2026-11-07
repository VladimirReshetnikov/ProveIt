#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-expression-eval-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'7b0b6e0e98340f3e14a77575fceb4e3f568f857d64fa1571fae6c4f79e175f49','source-manifest.json':'f82ff7187f433fcb2061b0ec20f222fde7f5c4b0620dfc656c149c2d40bb88b2','partial-survey.py':'14bf2ba8ea32195854fa2307eef0c485db28f7c28e519cfe0e782e3641cbde2b','seed-data-survey.py':'10ab328c0954fa189ba916747285f1b63cfa37dd08cce4df3f1fb9890a639d3b'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign25AbstractExpressionDef','Sign25AbstractExpressionEval','Sign25CurrentExpressionDef','Sign25CurrentExpressionEval'];assert [x['module'].split('.')[-1] for x in m]==names
ss=[]
for n,e in zip(names,m):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';assert H(p)==e['source_sha256']==H(D/f'research/nine-sharing-sign25-expression-eval-draft/{n}.lean');assert [x.split(' ',1)[1] for x in p.read_text().splitlines() if x.startswith('import ')]==e['imports'];ss.append(p.read_text())
a,b,c,d=ss
assert 'Expr (Fin 25)' in a
assert 'Sign32GenericRemoveInput.removeInput (SharingSeed25Octic.seed p)' in a
for x in ['(expression p).evalRing (fun i => ι (w i))','(SharingSeed25Octic.seed p).evalRing (fun i => ι (Fin.cons (1 : V) w i))','Sign32GenericRemoveInput.eval_removeInput','simp [map_one]']:assert x in b
assert 'Sign25AbstractExpression.expression CurrentWindowCarry2011.ports' in c
for x in ['(SharingSeed25Octic.seed CurrentWindowCarry2011.ports).evalRing','Fin.cons (1 : V) w i','Sign25AbstractExpression.eval_expression CurrentWindowCarry2011.ports w']:assert x in d
up=D/'reviews/nine-sharing-sign25-seed-squares-terminal-frontier-independent/check.py';assert H(up)=='8207d760d00d9df69137a6148da3565b8748afdf9246880eae8125feaabce9f9';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'abstract and current-port input=1 expression definitions/evaluation only; successful rows or observations of partially failed providers, no Lean replay'},sort_keys=True,indent=2))
