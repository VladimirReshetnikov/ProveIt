#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-expression-eval-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'618102d947c02971999ed8f0db3f7f551bdffa425c1e1d6a1052403638363196','source-manifest.json':'21d332d0b7ac4ad0ad328833a307dd8f14b75d3e8e0e3f035ddfa2d990b1e148','partial-survey.py':'368cf208a43b0a798b93f32bd839036f8407c8b9fc1543718ae9fa173ab20965','seed-data-survey.py':'7b9414ac436104231920b38fb25b4b712d2bf6ab7c92c2a725101016daf726ec'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign28AbstractExpressionDef','Sign28AbstractExpressionEval','Sign28CurrentExpressionDef','Sign28CurrentExpressionEval'];assert [r['module'].split('.')[-1] for r in m]==names
imps=[['Sign32GenericRemoveInput','SharingSeed28Sextic'],['Sign28AbstractExpressionDef'],['Sign28AbstractExpressionEval','CurrentKernelData2011'],['Sign28CurrentExpressionDef']];ss=[]
for row,n,deps in zip(m,names,imps):
 f=P/'src/DiophantineConsistency'/f'{n}.lean';s=f.read_text();ss.append(s);assert H(f)==row['source_sha256'] and row['imports']==['DiophantineConsistency.'+x for x in deps]
a,b,c,d=ss
assert 'Sign32GenericRemoveInput.removeInput (SharingSeed28Sextic.seed p)' in a and 'Expr (Fin 28)' in a
assert 'Sign32GenericRemoveInput.eval_removeInput' in b and 'Fin.cons (1 : V) w i' in b and 'funext i' in b and 'Fin.cases' in b
assert 'Sign28AbstractExpression.expression CurrentWindowCarry2011.ports' in c and 'Sign28AbstractExpression.eval_expression CurrentWindowCarry2011.ports w' in d and 'Fin.cons (1 : V) w i' in d
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':4,'scope':'abstract/current input-removal expression definitions and evaluations only'},sort_keys=True,indent=2))
