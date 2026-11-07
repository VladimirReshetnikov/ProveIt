#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-expression-eval-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6d4d52b69453c8ed0aad647ef47049a9995df3b5a50503988f758eb8c4209200','source-manifest.json':'72c64223011fe103fff449eb91ecbaf0b4fcc402d5c4993c446faabecb8a04f5','partial-survey.py':'627f360ae739f6e1bac7bf14d89687e963f299c81b81a7eb7492b2e09a0cb637','seed-data-survey.py':'40b06640255498a93f8a403f13108e6e09311ef6f5ab785b02205ea23a452d39'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign27AbstractExpressionDef','Sign27AbstractExpressionEval','Sign27CurrentExpressionDef','Sign27CurrentExpressionEval'];assert [x['module'].split('.')[-1] for x in m]==names
ss=[]
for n,e in zip(names,m):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';assert H(p)==e['source_sha256']==H(D/f'research/nine-sharing-sign27-expression-eval-draft/{n}.lean');assert [x.split(' ',1)[1] for x in p.read_text().splitlines() if x.startswith('import ')]==e['imports'];ss.append(p.read_text())
a,b,c,d=ss
assert 'Sign32GenericRemoveInput.removeInput (SharingSeed27Sextic.seed p)' in a
for x in ['(expression p).evalRing (fun i => ι (w i))','(SharingSeed27Sextic.seed p).evalRing (fun i => ι (Fin.cons (1 : V) w i))','Sign32GenericRemoveInput.eval_removeInput','simp [map_one]']:assert x in b
assert 'Sign27AbstractExpression.expression CurrentWindowCarry2011.ports' in c
for x in ['(SharingSeed27Sextic.seed CurrentWindowCarry2011.ports).evalRing','Fin.cons (1 : V) w i','Sign27AbstractExpression.eval_expression CurrentWindowCarry2011.ports w']:assert x in d
up=D/'reviews/nine-sharing-sign27-seed-squares-terminal-frontier-independent/check.py';assert H(up)=='b49e3c5c717922ed937f06ecf1a6ac3c0e781b825be50e2eb6f70728fefa42e8';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'abstract and current-port input=1 expression definitions/evaluation only; successful rows or observations of partially failed providers, no Lean replay'},sort_keys=True,indent=2))
