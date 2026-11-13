#!/usr/bin/env python3
"""Check exact inert source edit, finite residues, and bounded lexical source paths."""
from pathlib import Path
import collections,contextlib,hashlib,io,itertools,json,re,runpy
HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1]
ORIG=TASK/'research/adaptive87-four-square-current88-model-draft/FourUnitGeneric.lean.src'
SOURCE=TASK/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean'
FRONTIER=TASK/'research/adaptive87-four-square-provider-frontier-audit/result.json'
MODEL=TASK/'research/adaptive87-four-square-current88-model-draft/FourSquare88Model.lean.src'
NOZERO=TASK/'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean'
PINS={TASK/'research/adaptive87-four-square-provider-frontier-audit/check.py':'892f11eecd25f546e915e20d84c91ff06a6260b1cd206c21f980d32a4dce7686',
      MODEL:'973598a229e178097b3150169f0246d69bd7923d6026ee411f1e93bc1bbec45b',
      NOZERO:'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
      HERE/'FourSquare88Model.lean.src':'0a433997103bef6a946e61e75740161f67a0081c9e9ad22ddccbf9e2433225ee',
      ORIG:'50218ec01fc5e93bb78c31aaa9c8b21eae24a52c8ca524eaec36ef7219ee23d3',
      SOURCE:'9e80ae52f5dddd21d50684ebb6ca6556e95ac37905277bc476d251b7bf59f5a4',
      FRONTIER:'557e8fe54921a6f5a2cf3efb74afec46f462e12613dc25f91806471e6580d74b',
      HERE/'FourUnitGeneric.lean.src':'697261314731a6c93c8910b4d030ea116f4058a8d30a76843bfc1bbaefd26569'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,d in PINS.items():assert sha(p)==d,(p,sha(p))
source=SOURCE.read_text();old=ORIG.read_text();names=['first_bad','main_bad','strong_bad','aux_bad'];lemmas=[]
for n in names:
    matches=re.findall(r'^theorem '+n+r'\b.*? := by decide',source,re.M|re.S)
    assert len(matches)==1
    lemmas.append(matches[0].replace('theorem '+n,'private theorem '+n,1))
expected=old.replace('import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011','import Mathlib.Data.ZMod.Basic\nimport Mathlib.Tactic.LinearCombination\nimport Mathlib.Tactic.Linarith',1)
expected=expected.replace('open DiscreteOrderedRingFacts ArithmeticAdaptiveFactorUnits2011','open DiscreteOrderedRingFacts\n\n/- The next four finite residue facts are copied from\n   ArithmeticAdaptiveFactorUnits2011; only visibility is changed. -/\n'+'\n'.join(lemmas),1)
expected=expected.replace('Existing universal ZMod-4 exclusions','Local universal ZMod-4 exclusions',1)
assert (HERE/'FourUnitGeneric.lean.src').read_text()==expected
model=MODEL.read_text()
model=model.replace('import DiophantineConsistency.HAExpressionSameZero','import DiophantineConsistency.HAExpressionNoZeroEquiv',1)
model=model.replace('open HAExpressionAssembly HAExpressionSameZero PRALanguage IPRANativeTheory','open HAExpressionAssembly HAExpressionNoZeroEquiv PRALanguage IPRANativeTheory',1)
model=model.replace('theorem sameZero : HAExpressionSameZero.SameZero naturalExpression', '''/-- Same valuation in each model; local to avoid the 86-specific provider. -/
def SameZero {n : ℕ} (e g : Expr (Fin n)) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∀ v : Fin n → V, InternalZero e v ↔ InternalZero g v

theorem sameZero : SameZero naturalExpression''',1)
model=model.replace('    PolynomialBridge naturalExpression := HAExpressionSameZero.bridge _ _ sameZero hp', '''    PolynomialBridge naturalExpression := by
  apply HAExpressionNoZeroEquiv.bridge _ _ ?_ hp
  intro V _ _
  exact forall_congr' fun v => not_congr (sameZero V v)''',1)
assert model==(HERE/'FourSquare88Model.lean.src').read_text()
assert re.findall(r'^import (.+)$',NOZERO.read_text(),re.M)==['DiophantineConsistency.HAExpressionAssembly','DiophantineConsistency.AdaptiveEquationSyntax2011']
cases={'first_bad':0,'main_bad':0,'strong_bad':0,'aux_bad':0}
for q,z,n in itertools.product(range(4),repeat=3):
 assert (1+z*z-(q**3*(q-1))**2*n)%4!=3;cases['first_bad']+=1
for u,a,c,d in itertools.product(range(4),repeat=4):
 assert (1+d*d-u*u*(1+(a*a+4*a+3)*c*c))%4!=3;cases['main_bad']+=1
for a,f,i in itertools.product(range(4),repeat=3):
 assert (1+i*i-(a*a+4*a+3)*(f*f-1))%4!=3;cases['strong_bad']+=1
for a,f,v,y in itertools.product(range(4),repeat=4):
 delta=a*a+4*a+3
 assert (delta*(f*f-1)*v*v+(1-delta*(f*f-1))*y*y)%4!=3;cases['aux_bad']+=1
F=json.loads(FRONTIER.read_text()); graph=F['project_sources']|F['selected_modules']
# Pin all current source bytes represented by the predecessor lexical receipt.
for row in graph.values():assert sha(TASK/row['source'])==row['sha256'],row['source']
target='DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011'
def path(start):
    todo=collections.deque([(start,[start])]); seen=set()
    while todo:
        n,p=todo.popleft()
        if n in seen:continue
        seen.add(n)
        if n==target:return p
        todo.extend((v,p+[v]) for v in graph.get(n,{}).get('imports',[]))
    return None
roots=['AdaptiveFourSquare88Graph','DiophantineConsistency.AdaptiveFirstRootFactor87Literal','DiophantineConsistency.ModelCarrierScaled','DiophantineConsistency.HAExpressionSameZero','DiophantineConsistency.IPRAExpressionNative']
paths={n:path(n) for n in roots}
assert paths[roots[0]] is None and paths[roots[1]] is None and paths[roots[2]] is None
assert paths['DiophantineConsistency.HAExpressionSameZero'] is not None
# Swap only the actual import headers for the two proposed alternatives.
graph['FourUnitGeneric']={'imports':re.findall(r'^import (.+)$',(HERE/'FourUnitGeneric.lean.src').read_text(),re.M)}
graph['FourSquare88Model']={'imports':re.findall(r'^import (.+)$',(HERE/'FourSquare88Model.lean.src').read_text(),re.M)}
graph['DiophantineConsistency.HAExpressionNoZeroEquiv']={'imports':re.findall(r'^import (.+)$',NOZERO.read_text(),re.M)}
alternative_path=path('FourSquare88Model')
assert alternative_path is None
pending=collections.deque(['FourSquare88Model']); reached=set()
while pending:
    n=pending.popleft()
    if n in reached:continue
    reached.add(n);pending.extend(graph.get(n,{}).get('imports',[]))
project=sorted(n for n in reached if n.startswith('DiophantineConsistency.') and n in graph)
roots2={'ha87_historical':Path('/tmp/ha87-full-transitive-p3xt6wra/lib'),
        'current14_fresh_base':Path('/tmp/current14-standard-fresh-build-20261104/lib')}
status={key:{n:(root/Path(*n.split('.')).with_suffix('.olean')).is_file() for n in project}
        for key,root in roots2.items()}
both_missing=[n for n in project if not any(status[k][n] for k in status)]
overlap=[n for n in project if all(status[k][n] for k in status)]
provider_counts={k:{'present':sum(v.values()),'absent':len(v)-sum(v.values())} for k,v in status.items()}
# Recompute the complete source-declared project closure for the conditional
# client plus the actual proposed instantiation, without reusing its graph.
with contextlib.redirect_stdout(io.StringIO()):
    scanner=runpy.run_path(str(TASK/'research/adaptive87-four-square-provider-frontier-audit/check.py'))
source_imports=scanner['imports']
full_custom={'FourSquare88Model':HERE/'FourSquare88Model.lean.src',
             'FourUnitGeneric':HERE/'FourUnitGeneric.lean.src',
             'AdaptiveFourSquare88Graph':TASK/'research/adaptive87-four-square-current88-model-draft/AdaptiveFourSquare88Graph.lean.src'}
full_sources={}; external=set();missing=set(); todo=collections.deque(['FourSquare88Model','DiophantineConsistency.HAAdaptiveFactor87'])
while todo:
    n=todo.popleft()
    if n in full_sources or n in external or n in missing:continue
    if n in full_custom:p=full_custom[n]
    elif n.startswith('DiophantineConsistency.'):p=TASK/'Lean'/Path(*n.split('.')).with_suffix('.lean')
    else:external.add(n);continue
    if not p.is_file():missing.add(n);continue
    edges=source_imports(p);full_sources[n]={'source':str(p.relative_to(TASK)),'sha256':sha(p),'imports':edges}
    todo.extend(edges)
assert not missing,sorted(missing)
q=collections.deque([('DiophantineConsistency.HAAdaptiveFactor87',[])]);visited=set();endpoint_path=None
while q:
    n,previous=q.popleft()
    if n in visited:continue
    visited.add(n);way=previous+[n]
    if n==target:endpoint_path=way;break
    q.extend((child,way) for child in full_sources.get(n,{}).get('imports',[]))
assert endpoint_path is not None
full_project=sorted(n for n in full_sources if n.startswith('DiophantineConsistency.'))
full_status={key:{n:(root/Path(*n.split('.')).with_suffix('.olean')).is_file() for n in full_project}
             for key,root in roots2.items()}
full_counts={key:{'present':sum(v.values()),'absent':len(v)-sum(v.values())} for key,v in full_status.items()}
full_missing=[n for n in full_project if not any(full_status[k][n] for k in full_status)]
old_source=Path('/tmp/ha87-frozen-full-e_jgyudl/tree/Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean').read_text()
client=(TASK/'Lean/DiophantineConsistency/AdaptiveDirectOrdinate86Units.lean').read_text()
critical=['first_bad','main_bad','strong_bad','aux_bad','syntax_add','syntax_sub','syntax_mul','syntax_var','syntax_const','syntax_ofNat','factor0_eval','factor1_eval']
for n in critical:
    assert re.search(r'^private theorem '+n+r'\b',old_source,re.M),n
    assert re.search(r'^theorem '+n+r'\b',source,re.M),n
    assert re.search(r'\b'+n+r'\b',client),n
assert not re.search(r'^theorem units_of_residues\b',old_source,re.M)
assert re.search(r'^theorem units_of_residues\b',source,re.M)
assert re.search(r'\bunits_of_residues\b',client)
print(json.dumps({'status':'PASS','input_sha256':{str(k.relative_to(TASK)):v for k,v in PINS.items()},'exact_source_delta':True,'alternative_model_factorunits_path':alternative_path,'instantiated_endpoint_factorunits_path':endpoint_path,'instantiated_endpoint_project_source_count':len(full_project),'instantiated_endpoint_external_import_count':len(external),'instantiated_endpoint_external_import_names':sorted(external),'instantiated_endpoint_sources':full_sources,'instantiated_endpoint_provider_counts':full_counts,'instantiated_endpoint_missing_from_both_roots':full_missing,'alternative_project_source_count':len(project),'alternative_surveyed_provider_counts':provider_counts,'alternative_missing_from_both_project_roots':both_missing,'alternative_present_in_both_project_roots':overlap,'historically_private_used_by_86_client':critical,'units_of_residues_only_in_current_source_and_used_by_86_client':True,'finite_mod4_cases':cases,'lexical_paths_to_factor_units':paths,
 'limits':['Source-only; no Lean elaboration, object authentication, or provider consistency.',
 'No path found means none in the pinned predecessor lexical source closure, not no dynamic or package dependency.',
 'Original FourSquare88Model retains HAExpressionSameZero, whose source closure still reaches FactorUnits; the alternative omits that import.']},indent=2,sort_keys=True))
