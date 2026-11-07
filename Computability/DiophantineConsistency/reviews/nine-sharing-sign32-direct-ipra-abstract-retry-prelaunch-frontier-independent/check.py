#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign32-direct-ipra-abstract-retry';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'0c11306696ab068973592925f7e2d08e4431789264f365e222a78fb0769906ec','partial-survey.py':'00d919deb9204849c8f403a07d3c9e048ab817afc0ae6faed58e906de498b361','source-manifest.json':'252d46ac451146cebe87dfde723c90a13c83236ad45d96a453839c5224b8df4c'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];want=[('Sign32AbstractExpression','dfd16e0ec3767a632fdb7b2c36f9077b01e3e11ea466323c0f9b5d44d1c54b67',['Sign32GenericRemoveInput','Sign32CurrentSourceIff'],['eval_expression']),('Sign32CurrentExpressionDef','54fc7afff248cb6856e984380fd66ef0c032c290d1a5c200bd20214e5574b217',['Sign32AbstractExpression'],[]),('Sign32CurrentExpressionEval','4eefed610adcd4fcb4fb1c1c7e90190494f114cf4018448053db581a5e744550',['Sign32CurrentExpressionDef'],['eval_expression'])];assert len(rows)==3
for r,(n,h,im,ts) in zip(rows,want):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and r['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in im] and re.findall(r'^theorem (\w+)',s,re.M)==ts and len(re.findall(r'^#print axioms ',s,re.M))==len(ts)
a=(P/'src/DiophantineConsistency/Sign32AbstractExpression.lean').read_text();b=(P/'src/DiophantineConsistency/Sign32CurrentExpressionDef.lean').read_text();c=(P/'src/DiophantineConsistency/Sign32CurrentExpressionEval.lean').read_text()
for x in ['def expression (p : Fin 4 → ℤ) : Expr (Fin 32)','Sign32GenericRemoveInput.removeInput (SharingSeed32Sextic.seed p)','(fun i => ι (Fin.cons (1 : V) w i))','Sign32GenericRemoveInput.eval_removeInput']:assert x in a
assert 'def expression : Expr (Fin 32) := Sign32AbstractExpression.expression CurrentWindowCarry2011.ports' in b and 'attribute [local irreducible]' in b and 'theorem ' not in b
assert 'exact Sign32AbstractExpression.eval_expression CurrentWindowCarry2011.ports w' in c and 'attribute [local irreducible]' in c
R=D/'reviews/nine-sharing-sign32-direct-ipra-retry01-failure-frontier-independent';assert sha(R/'check.py')=='dacbf50d89c31cb777929781ac7518fd204444199a905d4861c54fb314b5f1a0' and sha(R/'result.json')=='0e91fac227aa38c19be9685e07b144dc61419565b81269b382f7a95790656171'
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==3
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'symbolic-port eval, closed current definition, current eval diagnostic; no source iff or endpoint'},indent=2,sort_keys=True))
