#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-named-equality-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ec56991abaea43920b0c54191b97d49a8a1c56c1463f91a8d47dc5ab6d436969','provider_preflight.py':'44932fd340a3a4d046c7598d4caabc9f3d9781d3a1ecfafae9cbaec2a77ac20f','source-manifest.json':'9dae6308341db7fb39bfeea192c8a77d9b17bea688c5ce76fc86a97df7982e0a'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];want=[('Norm38MacroNamedVars','7b2c1bf1208802cf92a6d9e795104abbff952cfabeac978f1afa8c97289e2e5b',['Norm38MacroVarsOutput','Norm38NamedFormula'],'vars_eq_named'),('Norm38MacroNamedEquality','e04fa148a65dfbe3cce2d641c7afb35fc547902822d829dad2b4d26c6ee2d2c4',['Norm38MacroNamedVars'],'recipe_eq_expression_eval')];assert len(rows)==2
for r,(n,h,im,t) in zip(rows,want):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and r['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in im] and re.findall(r'^theorem (\w+)',s,re.M)==[t]==re.findall(r'^#print axioms (\w+)',s,re.M)
a=(P/'src/DiophantineConsistency/Norm38MacroNamedVars.lean').read_text();b=(P/'src/DiophantineConsistency/Norm38MacroNamedEquality.lean').read_text();named=(D/'research/nine-seed38-jones-named-formula-check/src/DiophantineConsistency/Norm38NamedFormula.lean').read_text()
tuple1=a.split('def namedVars',1)[1].split(':=',1)[1].split('\ntheorem',1)[0];tuple2=named.split('theorem eval_current',1)[1].split('=\n',1)[1].split('RefinedPair.value',1)[0].replace('let v : RingVars R :=','');assert ''.join(tuple1.split())==''.join(tuple2.split())
assert 'vars a = namedVars a' in a and 'rw [d11_rank_symbolic]' in a and 'codingL4, codingLexp, base' in a
for x in ['Norm38MacroRecipe.recipe.values a (Fin.last 44) = Norm38IPRAEndpoint.expression.evalRing a','recipe_eq_refined a','rw [vars_eq_named]','(Norm38NamedFormula.eval_current a).symm']:assert x in b
assert '[CommRing R] (a : Fin 9 → R)' in a and '[CommRing R] (a : Fin 9 → R)' in b
print(json.dumps({'status':'PASS_STATIC','scope':'exact Lean recipe output equals Norm38 endpoint expression evaluation over all commutative rings; no JSON/human binding'},indent=2,sort_keys=True))
