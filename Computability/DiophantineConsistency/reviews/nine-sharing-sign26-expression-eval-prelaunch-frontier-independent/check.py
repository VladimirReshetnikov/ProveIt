#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-expression-eval-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'63563085b2ac9747057561b4ef780bd8d90ee75a61e8474a0df919906e8e88b8','source-manifest.json':'7ffa0ce5b148fe6e86a18719f50f4468f79e3a960b486a62dc635f1c6d805bda','partial-survey.py':'44c34680847c45ce846cbd1853cb819a3e2794ce64c91f810b7dc24a07455ba0','seed-data-survey.py':'d090d2f4a088f89f4c8f091bc6c9267ef4af28402a675c91631435287e1e809e'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign26AbstractExpressionDef','Sign26AbstractExpressionEval','Sign26CurrentExpressionDef','Sign26CurrentExpressionEval'];assert [x['module'].split('.')[-1] for x in m]==names
ss=[]
for n,e in zip(names,m):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';assert H(p)==e['source_sha256']==H(D/f'research/nine-sharing-sign26-expression-eval-draft/{n}.lean');assert [x.split(' ',1)[1] for x in p.read_text().splitlines() if x.startswith('import ')]==e['imports'];ss.append(p.read_text())
a,b,c,d=ss
assert 'Expr (Fin 26)' in a
assert 'Sign32GenericRemoveInput.removeInput (SharingSeed26Sextic.seed p)' in a
for x in ['(expression p).evalRing (fun i => ι (w i))','(SharingSeed26Sextic.seed p).evalRing (fun i => ι (Fin.cons (1 : V) w i))','Sign32GenericRemoveInput.eval_removeInput','simp [map_one]']:assert x in b
assert 'Sign26AbstractExpression.expression CurrentWindowCarry2011.ports' in c
for x in ['(SharingSeed26Sextic.seed CurrentWindowCarry2011.ports).evalRing','Fin.cons (1 : V) w i','Sign26AbstractExpression.eval_expression CurrentWindowCarry2011.ports w']:assert x in d
up=D/'reviews/nine-sharing-sign26-seed-squares-terminal-frontier-independent/check.py';assert H(up)=='a60bbcc769f385fd2ac4ac843ad661fa13a9668567e7f15157d3de4fa207911d';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'abstract and current-port input=1 expression definitions/evaluation only; successful rows or observations of partially failed providers, no Lean replay'},sort_keys=True,indent=2))
