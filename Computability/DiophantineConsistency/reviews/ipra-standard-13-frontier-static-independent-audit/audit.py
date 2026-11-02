#!/usr/bin/env python3
"""Independent static review of the pinned joint 13-variable author manifest."""
import copy,hashlib,importlib.util,json,re,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/ipra-standard-13-frontier';PARENT=Path('/tmp/ipra-aq29-fresh-source-closure-v2')
MANIFEST=TASK/'author-additions.json';DRIVER=BASE/'research/author-only-extension/run.py';PAIR_AUDIT=BASE/'reviews/fresh-project-pair-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text());pin='2a4749c34750dbff650e19b5e5fc7effd98a64774c4051852f3db39221b2f134'
inputs=[Path(__file__),MANIFEST,DRIVER,TASK/'build_manifest.py',TASK/'check_graphs.py',TASK/'graph-observation.json',TASK/'manifest-observation.json',PARENT/'manifest.json',PAIR_AUDIT/'receipt.json',PAIR_AUDIT/'terminal-observation.json']
spec=J(MANIFEST);parent=J(PARENT/'manifest.json');assert H(MANIFEST)==pin
assert H(PARENT/'manifest.json')==spec['parent_manifest_sha256']=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert J(PAIR_AUDIT/'terminal-observation.json')['exit_code']==0 and J(PAIR_AUDIT/'receipt.json')['status']=='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT'
assert spec['source_commit']=='72bb86f99414925806059a74f0bf77be7d1c5fc5' and spec['status']=='FROZEN_ADDITIONS'
short=['IPRASuccessorInduction','IPRAAddOneGeneral','IPRASuccessorInductionConverse','IPRAStandardTheory','AdaptiveDirectOrdinateSquareSumsLiteral','IPRASquareSumsNative','IPRAStandardSquareSums13','IPRAStandardProduct13']
names=['DiophantineConsistency.'+n for n in short]
assert spec['order']==names and set(spec['sources'])==set(names) and len(set(names))==8
sum_names=['DiophantineConsistency.IPRASquareSumsNative.'+x for x in ('sameZero','bridge','equivalence','literal_eq','literal_equivalence')]+[names[6]+'.'+x for x in ('literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency')]
product_names=['DiophantineConsistency.HAAdaptiveDirectOrdinate86.polynomialBridge']+[names[7]+'.'+x for x in ('native_equivalence','literal_equivalence','selected_foundation_consistency','literal_iff_translated_consistency')]
required={names[6]:sum_names,names[7]:product_names}
assert spec['axiom_reports']==required and sum(map(len,required.values()))==13
for name in names:inputs.append(ROOT/spec['sources'][name]['workspace_path'])
cases=[('sum87',BASE/'research/adaptive-square-sums/candidate.json',ROOT/spec['sources'][names[4]]['workspace_path'],'11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828','literal','\n\n/-- The generated DAG',87),('product86',BASE/'research/adaptive-direct-ordinate86/candidate.json',PARENT/'src/DiophantineConsistency/AdaptiveDirectOrdinate86Literal.lean','e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f','expressionAt86','\ndef contextAt',86)]
for _,g,s,_,_,_,_ in cases:inputs.extend((g,s))
inputs += [PARENT/'src/DiophantineConsistency/HAAdaptiveDirectOrdinate86.lean',PARENT/'src/DiophantineConsistency/CurrentKernelData2011.lean']
before={str(p.resolve()):H(p) for p in inputs};seen=set(parent['order']);assert len(seen)==1210 and not (seen&set(names))
blobs={};parent_edges=added_edges=0
for name in names:
 row=spec['sources'][name];path=ROOT/row['workspace_path'];blob=subprocess.run(['git','show',spec['source_commit']+':'+row['workspace_path']],cwd=ROOT,check=True,capture_output=True).stdout
 assert blob==path.read_bytes() and hashlib.sha256(blob).hexdigest()==row['sha256'];blobs[name]=blob.decode()
 imports=re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',blob.decode(),re.M)
 assert imports==row['imports'] and len(imports)==len(set(imports))
 for dep in imports:
  assert dep in seen,(name,dep)
  if dep in parent['sources']:parent_edges+=1
  else:added_edges+=1
 seen.add(name)
 printed=re.findall(r'^#print axioms\s+([A-Za-z_][A-Za-z0-9_.\']*)\s*$',blob.decode(),re.M)
 resolved=[n if n.startswith('DiophantineConsistency.') else name+'.'+n for n in printed]
 assert resolved==required.get(name,[]),(name,resolved)
assert 'DiophantineConsistency.HAAdaptiveDirectOrdinate86' in parent['sources']
# Traverse the complete declared parent dependency closure, not only the
# directly imported project modules. External/toolchain edges are recorded,
# not authenticated as package-transitive or dynamic loads.
front=[d for n in names for d in spec['sources'][n]['imports'] if d in parent['sources']];closure=set();external=set()
while front:
 n=front.pop()
 if n in closure:continue
 closure.add(n)
 for d in parent['sources'][n]['imports']:
  if d in parent['sources']:front.append(d)
  else:external.add(d)
assert all(n in parent['sources'] for n in closure) and 'DiophantineConsistency.HAAdaptiveDirectOrdinate86' in closure
# Parse both literal bodies as operations, independently of the generator.
def parse_graph(graph,source,definition,end,count):
 signature=f'def {definition} (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n';assert source.count(signature)==1
 body=source.split(signature,1)[1].split(end,1)[0].strip().splitlines();variables=[];ports=[];operations=[];output=None
 for line in body:
  line=line.strip();m=re.fullmatch(r'let (\w+) : Expr \(Fin 13\) := \.var (\d+)',line)
  if m:variables.append((m[1],int(m[2])));continue
  m=re.fullmatch(r'let (\w+) : Expr \(Fin 13\) := \.constant \(p (\d+)\)',line)
  if m:ports.append((m[1],int(m[2])));continue
  m=re.fullmatch(r'let (\w+) := (\w+) ([+*\-]) (\w+)',line)
  if m:operations.append([m[1],m[3],int(m[2]) if m[2].isdigit() else m[2],int(m[4]) if m[4].isdigit() else m[4]]);continue
  assert output is None and re.fullmatch(r'\w+',line);output=line
 assert variables==list(zip(graph['witnesses'],range(13))) and len(set(graph['witnesses']))==13
 assert ports==list(zip(graph['fixed_numerals'],range(4))) and operations==graph['source'] and len(operations)==count and output==graph['output']
for label,g,src,sha,definition,end,count in cases:
 assert H(g)==sha and len(J(g)['source'])==count
 if label=='product86':assert H(src)==parent['sources']['DiophantineConsistency.AdaptiveDirectOrdinate86Literal']['sha256']
 graph=J(g);text=src.read_text();parse_graph(graph,text,definition,end,count)
 for old,new in (('.var 0','.var 1'),('.constant (p 0)','.constant (p 1)'),('let qm := J * beta','let qm := J + beta')):
  changed=text.replace(old,new,1);assert changed!=text
  try:parse_graph(graph,changed,definition,end,count)
  except AssertionError:pass
  else:raise AssertionError((label,'mutation accepted'))
# Bind selected native and standard theorem spellings and product shift.
sumnative=blobs[names[5]];square=blobs[names[6]];product=blobs[names[7]]
assert ('theorem literal_equivalence : nativeTheory ⊢\n'
        '    IPRAExpressionNative.nativeNoZero (AdaptiveEquationSyntax2011.positiveShift\n'
        '      (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘\n'
        '      ∼mappedNativeRefutation embedding := by') in sumnative
assert ('theorem literal_equivalence : standardTheory ⊢ IPRAExpressionNative.nativeNoZero\n'
        '    (positiveShift (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘\n'
        '      ∼mappedNativeRefutation embedding :=') in square
assert ('theorem literal_iff_translated_consistency : standardTheory ⊢\n'
        '    IPRAExpressionNative.nativeNoZero\n'
        '      (positiveShift (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘\n'
        '        (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=') in square
assert 'theorem native_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero\n    AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘 ∼mappedNativeRefutation embedding :=' in product
assert 'theorem literal_equivalence : standardTheory ⊢ IPRAExpressionNative.nativeNoZero\n    AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘 ∼mappedNativeRefutation embedding :=' in product
assert ('theorem literal_iff_translated_consistency : standardTheory ⊢\n'
        '    IPRAExpressionNative.nativeNoZero AdaptiveDirectOrdinate86Literal.naturalExpression86 🡘\n'
        '      (Semiformula.lMap embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ :=') in product
assert 'def naturalExpression86 : Expr (Fin 13) := AdaptiveEquationSyntax2011.positiveShift expression86' in cases[1][2].read_text()
# The generic source validator checks structure; the task-specific exact names
# and fixed digest must also be enforced. Exercise both layers separately.
module_spec=importlib.util.spec_from_file_location('guarded_author_runner',DRIVER);runner=importlib.util.module_from_spec(module_spec);module_spec.loader.exec_module(runner)
actual_names,_=runner.verify_additions(spec,ROOT);assert actual_names==names
for kind in ('duplicate_module','source_hash','wrong_import','duplicate_report','outside_report'):
 bad=copy.deepcopy(spec)
 if kind=='duplicate_module':bad['order'].append(bad['order'][0])
 if kind=='source_hash':bad['sources'][names[0]]['sha256']='0'*64
 if kind=='wrong_import':bad['sources'][names[0]]['imports'].append('DiophantineConsistency.Forged')
 if kind=='duplicate_report':bad['axiom_reports'][names[7]].append(bad['axiom_reports'][names[7]][0])
 if kind=='outside_report':bad['axiom_reports']['DiophantineConsistency.Forged']=['DiophantineConsistency.Forged.x']
 try:runner.verify_additions(bad,ROOT)
 except ValueError:pass
 else:raise AssertionError(('runner accepted invalid metadata',kind))
def exact_policy(candidate):
 if candidate['order']!=names or candidate['axiom_reports']!=required:raise ValueError('task policy mismatch')
# The generic validator intentionally does not know this task's exact report
# list. Demonstrate that its acceptance of a structurally valid weakened list
# must be supplemented by the independently anchored manifest digest and the
# driver's later exact comparison of reports with compiled logs.
weakened=copy.deepcopy(spec);weakened['axiom_reports'][names[7]].pop()
assert runner.verify_additions(weakened,ROOT)[0]==names
assert hashlib.sha256((json.dumps(weakened,indent=2,sort_keys=True)+'\n').encode()).hexdigest()!=pin
try:exact_policy(weakened)
except ValueError:pass
else:raise AssertionError('weakened task policy accepted')
for kind in ('missing_report','changed_report','wrong_order','added_silent_report'):
 bad=copy.deepcopy(spec)
 if kind=='missing_report':bad['axiom_reports'][names[7]].pop()
 if kind=='changed_report':bad['axiom_reports'][names[6]][0]='DiophantineConsistency.Forged.x'
 if kind=='wrong_order':bad['order'][0],bad['order'][1]=bad['order'][1],bad['order'][0]
 if kind=='added_silent_report':bad['axiom_reports'][names[0]]=['DiophantineConsistency.Forged.x']
 assert hashlib.sha256((json.dumps(bad,indent=2,sort_keys=True)+'\n').encode()).hexdigest()!=pin
 try:exact_policy(bad)
 except ValueError:pass
 else:raise AssertionError(('task-specific policy mutation accepted',kind))
assert {str(p.resolve()):H(p) for p in inputs}==before
result={'status':'PASS_INDEPENDENT_FRONTIER13_STATIC_AUDIT','inputs_sha256':before,'manifest_sha256':pin,'source_commit':spec['source_commit'],
        'modules':8,'reports':13,'direct_parent_edges':parent_edges,'direct_added_edges':added_edges,'parent_declared_closure':len(closure),'external_declared_modules':len(external),
        'graph_operations':{'sum87':87,'product86':86},'graph_mutations_rejected':6,'runner_metadata_mutations_rejected':5,'exact_policy_mutations_rejected':4,
        'weakened_report_list_accepted_by_generic_source_validator':True,
        'scope':'Static pinned source, graph and manifest review; no guarded Lean result, matched replay, formal PDF semantics, or package-transitive/dynamic provenance claim.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
