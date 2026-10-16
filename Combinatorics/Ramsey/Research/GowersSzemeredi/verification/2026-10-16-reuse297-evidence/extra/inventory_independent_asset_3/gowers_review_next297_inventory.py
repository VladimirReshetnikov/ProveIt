import sys;sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,subprocess,copy,collections,re,ast,datetime
ROOT=Path('/home/codex/.codex/worktrees/9c9b/Proofs');SOURCE='c0592870a91dd586ffdb2565e176807c2c30ff5b';OUT=Path('/tmp/gowers-next297-integrated-inventory-independent-review')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pairs(items):
 d={}
 for k,v in items:assert k not in d,k;d[k]=v
 return d
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=pairs)
def exact(a,b):return json.dumps(a,ensure_ascii=False)==json.dumps(b,ensure_ascii=False)
def canon(x):return json.dumps(x,sort_keys=True,ensure_ascii=False)
rawp=Path('/tmp/gowers-next297-integrated-inventory-actual/raw.json');normp=Path('/tmp/gowers-next297-integrated-inventory-compared/normalized.json');compp=normp.parent/'comparison.json';genp=rawp.parent/'generator-receipt.json';helper=Path('/tmp/gowers-reuse135-inventory-comparison-tools-repaired703b/compare_inventory.py')
pins={str(rawp):'4a351aa79438c5f2a0748591fad3eb5c695b1f3101e613f97ffe6047212f4005',str(normp):'6ba9ef5ed2fd95dab508eae0b2ee15191ef7e2795da094c0286b4b413266b812',str(compp):'cb6a383131805dcdd0541a4682a4a8293cf50662ab984cc5f9a35c4d19d65bb6',str(genp):'e2eebfc98e271bb94c4599d8b3386f3001a2ec3b144935664f90369013c9b3aa',str(helper):'b4e0189104e0b696b2f54608cf9ba8a5a8ea4cf0200fbc0ec550eb1ed8d0a8be'}
for p,h in pins.items():assert sha(p)==h,p
raw=read(rawp);norm=read(normp);comp=read(compp);gen=read(genp)
basebytes=subprocess.check_output(['git','show',SOURCE+':Combinatorics/Ramsey/gowers-proof-status.json'],cwd=ROOT);base=json.loads(basebytes,object_pairs_hook=pairs);assert hashlib.sha256(basebytes).hexdigest()=='4af771fc97ac61b9714240cbf90bd2772ce390c6c73ae1510b64aaa78d071144'==comp['baseline']['sha256']
assert comp['source_commit']==gen['source_commit']==SOURCE
assert type(gen['terminal_exit'])is int and gen['terminal_exit']==0 and gen['native_validation_pending']is True
assert gen['raw_path']==str(rawp)and gen['raw_sha256']==sha(rawp)
assert gen['command'][1]=='Combinatorics/Ramsey/scripts/gowers_status.py'and Path(gen['command'][0]).name.startswith('python')and len(gen['command'])==2
assert sha(ROOT/gen['command'][1])==gen['generator_sha256']=='c03e1a7df0bb38de346a03f5cc2075bb0f97a739447479e06f7753c42ce4b47d'
assert datetime.datetime.fromisoformat(gen['started_at'])<=datetime.datetime.fromisoformat(gen['finished_at'])
assert sha(gen['stderr_path'])==gen['stderr_sha256']and Path(gen['stderr_path']).read_bytes()==b''
assert len(base['statements'])==len(raw['statements'])==len(norm['statements'])==120
assert [x['statement']for x in base['statements']]==[x['statement']for x in raw['statements']]==[x['statement']for x in norm['statements']]
assert list(base)==list(raw)==list(norm)
assert len(comp['permutations'])==4
reconstructed=copy.deepcopy(raw);paths=[]
for item in comp['permutations']:
 p=item['path'];assert len(p)==3 and p[0]=='statements'and p[2]in['exact_companions','related_theorems'];assert p not in paths;paths.append(p)
 a=raw['statements'][p[1]][p[2]];b=norm['statements'][p[1]][p[2]];order=item['raw_indices_in_baseline_order'];assert all(type(i)is int for i in order)and sorted(order)==list(range(len(a)));assert len(a)==item['occurrence_count'];assert exact([a[i]for i in order],b);assert collections.Counter(map(canon,a))==collections.Counter(map(canon,b));reconstructed['statements'][p[1]][p[2]]=[copy.deepcopy(a[i])for i in order]
assert exact(reconstructed,norm)
occ=0;duplicates=[]
for i,(a,b,c)in enumerate(zip(base['statements'],raw['statements'],norm['statements'])):
 for k in ['exact_companions','related_theorems']:
  assert len(a[k])==len(b[k])==len(c[k]);occ+=len(c[k]);assert [x['name']for x in a[k]]==[x['name']for x in c[k]];assert collections.Counter(map(canon,b[k]))==collections.Counter(map(canon,c[k]))
  for obj,count in collections.Counter(map(canon,c[k])).items():
   if count>1:duplicates.append(dict(path=['statements',i,k],object=json.loads(obj),multiplicity=count))
assert occ==544
# Independent typed/order-preserving full recursive comparison.
def differences(a,b,path=[]):
 assert type(a)is type(b),path
 if isinstance(a,dict):assert list(a)==list(b),path;return [d for k in a for d in differences(a[k],b[k],path+[k])]
 if isinstance(a,list):assert len(a)==len(b),path;return [d for i in range(len(a))for d in differences(a[i],b[i],path+[i])]
 return []if a==b else [dict(path=path,before=a,after=b)]
changes=differences(base,norm);assert len(changes)==37 and exact(changes,comp['location_leaf_changes'])
for c in changes:assert c['path'][-1]in['line','file']
# Pinned pure functions only: no main/top-level execution or generator/native invocation.
ns=dict(Path=Path,Counter=collections.Counter,defaultdict=collections.defaultdict,copy=copy,json=json,re=re,ROOT=ROOT,SOURCE=ROOT/'Combinatorics/Ramsey/Lean/GowersSzemeredi',sha=sha,canonical=canon)
tree=ast.parse(helper.read_text());names={'differences','array_order','normalize','verify_locations'};nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name in names];assert len(nodes)==4
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'),ns)
n,p,c=ns['normalize'](base,raw);assert exact(n,norm)and exact(p,comp['permutations'])and exact(c,changes)
sourcepins=ns['verify_locations'](raw);assert sourcepins==comp['source_location_files']and len(sourcepins)==288
for p,h in sourcepins.items():assert sha(p)==h,p
six=read('/tmp/gowers-next-reuse286-composition/inventory-projection.json')['incremental_location_changes'];assert len(six)==6
for c in six:assert c in changes,c
incoming=[c for c in changes if c not in six];assert len(incoming)==31
for p,h in pins.items():assert sha(p)==h,p
OUT.mkdir(exist_ok=False)
(OUT/'baseline-at-source-commit.json').write_bytes(basebytes)
report=dict(status='PASS: independent source inventory ordering/location review; native validation pending',findings=[],source_commit=SOURCE,input_pins=pins,baseline=dict(path=str(OUT/'baseline-at-source-commit.json'),sha256=sha(OUT/'baseline-at-source-commit.json'),retrieved_from_git=SOURCE+':Combinatorics/Ramsey/gowers-proof-status.json'),rows=120,whole_companion_occurrences=544,whole_object_permutations=comp['permutations'],whole_raw_objects_and_multiplicity_preserved=True,all_ordered_row_keys_and_semantic_qualification_status_fields_exact=True,baseline_to_normalized_location_leaf_count=37,incoming_location_leaves=incoming,NEXT297_inherited_six_location_leaves=six,normalized_sha256=sha(normp),source_location_files_verified=288,all120_catalogue_definitions_and544_theorem_or_alias_locations_verified=True,alias_companion_preserved=True,pinned_pure_function_normalize_result_reproduced=True,generator_receipt_raw_source_command_stderr_linkage_verified=True,limits=['This review certifies source inventory content, ordering and declaration locations only. It does not certify kernel/native success.','The preserved baseline is the inventory in source commitc059, hash4af771fc. The live repository inventory was already normalized when checked; no assumption that live inventory remains baseline is made.','The six NEXT297 changes are exactly the six already reviewed NEXT286 location leaves; the other31 changes are distinct incoming-source locations.'],no_native_generator_candidate_entrypoint_or_source_git_cache_mutation=True,review_script=dict(path=str(Path(__file__)),sha256=sha(__file__)))
(OUT/'report.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');(OUT/'review.txt').write_text('PASS source-only inventory review. Exact120 ordered rows and544 whole companion occurrences retained. Four inspected whole-object permutations at related_theorems rows26,78,79,85 reproduce the normalized inventory exactly, preserving duplicate multiplicity. Full typed recursive comparison gives37 location-only leaves, split31 incoming and6 NEXT297. All120 catalogue definition locations and544 theorem/alias locations in288 source files verified. No semantic/qualification/status change or native success claim.\n');(OUT/'freeze.json').write_text(json.dumps({'assets':[{'path':str(p),'sha256':sha(p)}for p in sorted(OUT.iterdir())if p.is_file()],'review_script':{'path':str(Path(__file__)),'sha256':sha(__file__)}},indent=2)+'\n')
print(json.dumps({'report_path':str(OUT/'report.json'),'report_sha256':sha(OUT/'report.json'),'freeze_sha256':sha(OUT/'freeze.json'),'permutation_rows':[p[1]for p in paths],'rows':120,'occurrences':544,'location_changes':37,'source_location_files':288},indent=2))
