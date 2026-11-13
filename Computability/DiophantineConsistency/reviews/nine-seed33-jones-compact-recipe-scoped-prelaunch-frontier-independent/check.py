#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-recipe-scoped-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P/'run.py')=='4cb59c1e972474df745562b764d01afb4ac711b82fdfc57e8fcade0c07bfb225' and sha(P/'source-manifest.json')=='0fbbc1930b8922b725f0937528d73d930ac5912733315c59c2f9217959edd396'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroRecipe','Sign33MacroScoped'];src=[]
for r in m:
 n=r['module'].split('.')[-1];p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();src.append(s);assert sha(p)==r['source_sha256'];assert [x[7:] for x in s.splitlines() if x.startswith('import ')]==r['imports']
a,b=src;full=(D/'research/nine-seed33-jones-compact-lean-specialized-draft/Sign33MacroRecipe.lean').read_text();removed='/-- Open proposition: compact graph evaluation equals the checked endpoint. -/\ndef SemanticTarget : Prop :=\n  ∀ (R : Type) [CommRing R] (a : Fin 9 → R),\n    recipe.values a (Fin.last 44) = Sign33IPRAEndpoint.expression.evalRing a\n\n';assert full.count(removed)==1 and full.replace(removed,'')==a and sum(' := .snoc ' in line for line in a.splitlines())==45 and 'def WellScopedTarget : Prop := recipe.scoped = true' in a
assert 'theorem recipe_well_scoped : Sign33MacroRecipe.WellScopedTarget' in b and 'change Sign33MacroRecipe.recipe.scoped = true' in b and '  decide' in b and b.count('#print axioms')==1
print(json.dumps({'status':'PASS_STATIC','scope':'45-node Lean recipe data and proposed Boolean scopedness only; semantic equality and JSON binding remain open'}))
