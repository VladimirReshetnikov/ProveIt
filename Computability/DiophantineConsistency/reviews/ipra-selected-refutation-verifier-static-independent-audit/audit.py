#!/usr/bin/env python3
"""Static review only: selected checker statement, manifest, and pinned ancestry."""
import copy, hashlib, importlib.util, json, re, subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency'
TASK=BASE/'research/ipra-selected-refutation-verifier'; MANIFEST=TASK/'author-additions.json';DRIVER=BASE/'research/author-only-extension/run.py'
PARENT=Path('/tmp/ipra-aq29-fresh-source-closure-v2'); OLD=BASE/'research/ipra-standard-13-frontier/author-additions.json'
PIN='dae80b2f3bc452f6138da34e5af026c458c7464bdee1b9a1bb9e0d02ca70a7c2'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
J=lambda p:json.loads(Path(p).read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
assert H(MANIFEST)==PIN and H(OLD)=='2a4749c34750dbff650e19b5e5fc7effd98a64774c4051852f3db39221b2f134'
assert H(PARENT/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert git('show','bc6006ceb2:Computability/DiophantineConsistency/research/ipra-selected-refutation-verifier/author-additions.json')==MANIFEST.read_bytes()
m=J(MANIFEST);old=J(OLD);parent=J(PARENT/'manifest.json')
assert m['status']=='FROZEN_ADDITIONS' and m['source_commit']=='6225789d20ea07daa453e27e690a6d6ce269119b'
assert m['parent_manifest_sha256']==old['parent_manifest_sha256']=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
prefix='DiophantineConsistency.'; additions=[prefix+'IPRASelectedMatrixCharacteristic',prefix+'IPRASelectedCheckerConsistency']
names=old['order']+additions
assert m['order']==names and len(names)==len(set(names))==10 and set(m['sources'])==set(names)
for n in old['order']:assert m['sources'][n]==old['sources'][n]
expected=copy.deepcopy(old['axiom_reports']); expected[additions[0]]=[additions[0]+'.selected_matrix_characteristic',additions[0]+'.selected_bounded_negation'];expected[additions[1]]=[additions[1]+'.selected_checker_endpoints']
assert m['axiom_reports']==expected and sum(map(len,expected.values()))==16
inputs=[Path(__file__),MANIFEST,OLD,DRIVER,PARENT/'manifest.json',BASE/'reviews/ipra-standard-13-frontier-static-independent-audit/receipt.json']
inputs += [ROOT/m['sources'][n]['workspace_path'] for n in names]
refs=['FoundationHAConsistencyNormalization','IPRAFoundationZFCWitnessBound','IPRAFoundationZFCMappedNegation','PRACharacteristicBit','IPRACharacteristicTransfer','IPRABoundedShape']
for name in refs:
 p=PARENT/'src/DiophantineConsistency'/(name+'.lean');assert H(p)==parent['sources'][prefix+name]['sha256'];inputs.append(p)
before={str(p.resolve()):H(p) for p in inputs};seen=set(parent['order']);assert len(seen)==1210 and not seen.intersection(names)
blobs={};parent_edges=added_edges=0
for name in names:
 row=m['sources'][name];p=ROOT/row['workspace_path'];raw=git('show',m['source_commit']+':'+row['workspace_path'])
 assert raw==p.read_bytes() and hashlib.sha256(raw).hexdigest()==row['sha256'];text=raw.decode();blobs[name]=text
 imports=re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',text,re.M)
 assert imports==row['imports'] and len(imports)==len(set(imports))
 for d in imports:
  assert d in seen,(name,d)
  if d in parent['sources']:parent_edges+=1
  else:added_edges+=1
 seen.add(name)
 printed=re.findall(r'^#print axioms\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',text,re.M)
 resolved=[x if x.startswith(prefix) else name+'.'+x for x in printed]
 assert resolved==expected.get(name,[]),(name,resolved)
front=[d for n in names for d in m['sources'][n]['imports'] if d in parent['sources']];closure=set();external=set()
while front:
 n=front.pop()
 if n in closure:continue
 closure.add(n)
 for d in parent['sources'][n]['imports']:
  if d in parent['sources']:front.append(d)
  else:external.add(d)
assert set(prefix+x for x in refs)<=closure
# Check exactly one existentially selected code, one classical PRA bit claim,
# and same-code native and standard negated checker and endpoint statements.
M=blobs[additions[0]];C=blobs[additions[1]]
def statement(text,name):
 s=text.split('theorem '+name+' :',1);assert len(s)==2
 h=s[1].split(':= by',1);assert len(h)==2
 return ' '.join(h[0].split())
def check_matrix(text):
 s=statement(text,'selected_matrix_characteristic')
 assert s==('∃ c : Code 1, Primrec (PRAFiniteFunctionCodes.eval c) ∧ PRA ⊢ PRACharacteristicBit.bitSentence c ∧ '
  '∀ e : Fin 1 → Term language ℕ, extended nativeTheory ⊢ native (Rew.embSubsts e ▹ oneAtom c) 🡘 '
  'native (Rew.embSubsts e ▹ (Semiformula.lMap embedding (bnd rho)))')
 assert 'IPRABoundedShape.boundedCharacteristicAny φ hφ' in text and 'transferCorrectness c φ hc e' in text
 assert statement(text,'selected_bounded_negation')==('nativeTheory ⊢ ∼mappedNativeRefutation embedding 🡘 ∼native (Semiformula.lMap embedding boundedRefutation)')
def check_checker(text):
 assert 'def checkerRefutation (c : Code 1) : Sentenceᵢ language := ∃⁰ native (oneAtom c)' in text
 assert statement(text,'selected_checker_endpoints')==('∃ c : Code 1, Primrec (PRAFiniteFunctionCodes.eval c) ∧ PRA ⊢ PRACharacteristicBit.bitSentence c ∧ '
  'nativeTheory ⊢ (∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c) ∧ '
  'standardTheory ⊢ (∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c) ∧ '
  'standardTheory ⊢ (IPRAExpressionNative.nativeNoZero (AdaptiveEquationSyntax2011.positiveShift (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘 ∼checkerRefutation c) ∧ '
  'standardTheory ⊢ (IPRAExpressionNative.nativeNoZero AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘 ∼checkerRefutation c)')
 for n in ('selected_matrix_characteristic','selected_bounded_negation','provable_iff _','IPRAStandardSquareSums13.literal_equivalence','IPRAStandardProduct13.literal_equivalence'):assert n in text
check_matrix(M);check_checker(C)
for oldfrag,newfrag,fun,text in [
 ('PRA ⊢ PRACharacteristicBit.bitSentence c','nativeTheory ⊢ PRACharacteristicBit.bitSentence c',check_matrix,M),
 ('∼mappedNativeRefutation embedding 🡘 ∼checkerRefutation c','mappedNativeRefutation embedding 🡘 checkerRefutation c',check_checker,C),
 ('AdaptiveDirectOrdinate86Literal.naturalExpression86','AdaptiveDirectOrdinate86Literal.expression86',check_checker,C),
 ('∃ c : Code 1','∀ c : Code 1',check_checker,C)]:
 changed=text.replace(oldfrag,newfrag,1);assert changed!=text
 try:fun(changed)
 except AssertionError:pass
 else:raise AssertionError(('statement mutation accepted',oldfrag))
parenttext={n:(PARENT/'src/DiophantineConsistency'/(n+'.lean')).read_text() for n in refs}
assert 'def bitSentence' in parenttext['PRACharacteristicBit'] and 'PRA ⊢ bitSentence' in parenttext['PRACharacteristicBit']
assert 'def oneAtom' in parenttext['IPRACharacteristicTransfer'] and 'applyCode c (vars n)' in parenttext['IPRACharacteristicTransfer']
assert 'noncomputable def boundedRefutation : ArithmeticSentence := ∃⁰ (bnd rho)' in parenttext['IPRAFoundationZFCWitnessBound']
assert 'provabilityPred (LO.FirstOrder.SetTheory.ZermeloFraenkelChoice' in parenttext['FoundationHAConsistencyNormalization']
assert 'source_eq_neg_rho : sourceSentence = ∼rho' in parenttext['FoundationHAConsistencyNormalization']
# Source validator is structural; task-specific complete report list is pinned separately.
spec=importlib.util.spec_from_file_location('runner',DRIVER);runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
assert runner.verify_additions(m,ROOT)[0]==names
for kind in ('duplicate','source_hash','wrong_import','duplicate_report','outside_report'):
 x=copy.deepcopy(m)
 if kind=='duplicate':x['order'].append(x['order'][0])
 if kind=='source_hash':x['sources'][names[0]]['sha256']='0'*64
 if kind=='wrong_import':x['sources'][names[0]]['imports'].append(prefix+'Forged')
 if kind=='duplicate_report':x['axiom_reports'][additions[1]].append(x['axiom_reports'][additions[1]][0])
 if kind=='outside_report':x['axiom_reports'][prefix+'Forged']=[prefix+'Forged.x']
 try:runner.verify_additions(x,ROOT)
 except ValueError:pass
 else:raise AssertionError(('invalid metadata accepted',kind))
x=copy.deepcopy(m);x['axiom_reports'][additions[0]].pop()
assert runner.verify_additions(x,ROOT)[0]==names
assert hashlib.sha256((json.dumps(x,sort_keys=True,indent=2)+'\n').encode()).hexdigest()!=PIN and x['axiom_reports']!=expected
assert {str(p.resolve()):H(p) for p in inputs}==before
result={'status':'PASS_INDEPENDENT_SELECTED_CHECKER_STATIC_AUDIT','inputs_sha256':before,'manifest_sha256':PIN,'source_commit':m['source_commit'],'modules':10,'reports':16,'direct_parent_edges':parent_edges,'direct_added_edges':added_edges,'parent_declared_closure':len(closure),'external_declared_modules':len(external),'statement_mutations_rejected':4,'runner_metadata_mutations_rejected':5,'weakened_report_list_accepted_by_generic_source_validator':True,'scope':'Static source and pinned manifest review only; no guarded replay or paired result; selected bound checker only; classical PRA bit theorem; no arbitrary-checker comparison or PDF transcription claim.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
