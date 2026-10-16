"""Independent ordered inventory/data/source-location checks; no helper execution."""
from pathlib import Path
from collections import Counter,defaultdict,deque
import json,hashlib,re,datetime,copy
ROOT=Path('/home/codex/.codex/worktrees/9c9b/Proofs')
INP=Path('/tmp/gowers-merge04fd-inventory-actual')
OUT=Path('/tmp/gowers-merge04fd-inventory-independent-review')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pairs(items):
 d={}
 for k,v in items:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=pairs)
def canonical(v):return json.dumps(v,sort_keys=True,ensure_ascii=False,separators=(',',':'))
pins={}
def pin(p,h):
 assert sha(p)==h,str(p)
 pins[str(p)]=h
def write(n,obj):
 p=OUT/n
 with p.open('x') as f:json.dump(obj,f,indent=2,ensure_ascii=False);f.write('\n')
 p.chmod(0o444)
pin(INP/'generator-receipt.json','074802bc4bbaf421f35d0b2251b038423a397caf12e132e26d980a21bd9132ba')
pin(INP/'comparison.json','42d4e89374878db9728bdf4f43e1ba98195a5fa98250106d82ff4cd40636d432')
pin(INP/'normalized.json','d705215fb1fe2edb737ff21e464913e0823d6c5b682de168eddbc6146d0ffadd')
gen=read(INP/'generator-receipt.json');cmp=read(INP/'comparison.json')
assert gen['base_commit']==cmp['base_commit']=='cb7319ce84f72719fa92797c689591a29e547d40'
assert gen['merge_head']==cmp['merge_head']=='04fd0fb36e46ff05373664236758eff99665bded'
assert gen['status']=='Actual source inventory generation only; no merged-source native validation'
assert type(gen['terminal_exit']) is int and gen['terminal_exit']==0
assert gen['command']==['/home/codex/.local/bin/python3','Combinatorics/Ramsey/scripts/gowers_status.py']
assert datetime.datetime.fromisoformat(gen['started_at'])<=datetime.datetime.fromisoformat(gen['finished_at'])
assert gen['raw_path']==str(INP/'raw.json') and gen['stderr_path']==str(INP/'generator.stderr')
pin(INP/'baseline.json',gen['baseline_sha256'])
assert gen['baseline_sha256']=='d416811dbefdfce7b96b7b0b10d9200422fca4688dc2e193b47c1a0c18d158bd'
pin(INP/'raw.json',gen['raw_sha256']);pin(INP/'generator.stderr',gen['stderr_sha256'])
assert (INP/'generator.stderr').read_bytes()==b''
pin(ROOT/'Combinatorics/Ramsey/scripts/gowers_status.py',gen['generator_sha256'])
assert gen['generator_sha256']=='c03e1a7df0bb38de346a03f5cc2075bb0f97a739447479e06f7753c42ce4b47d'
pin('/tmp/gowers-reuse135-inventory-comparison-tools-repaired703b/compare_inventory.py',cmp['helper_sha256'])
assert cmp['helper_sha256']=='b4e0189104e0b696b2f54608cf9ba8a5a8ea4cf0200fbc0ec550eb1ed8d0a8be'
inventory=ROOT/'Combinatorics/Ramsey/gowers-proof-status.json'
pin(inventory,cmp['normalized_sha256'])
assert inventory.read_bytes()==(INP/'normalized.json').read_bytes()
old=read(INP/'baseline.json');raw=read(INP/'raw.json');new=read(INP/'normalized.json')
assert len(old['statements'])==len(raw['statements'])==len(new['statements'])==120
assert [r['statement'] for r in old['statements']]==[r['statement'] for r in raw['statements']]==[r['statement'] for r in new['statements']]
assert new['counts']==old['counts']=={'exact_companion':120}
def diffs(a,b,path=()):
 assert type(a) is type(b),path
 if isinstance(a,dict):
  assert list(a)==list(b),path
  return [d for k in a for d in diffs(a[k],b[k],path+(k,))]
 if isinstance(a,list):
  assert len(a)==len(b),path
  return [d for n,(x,y) in enumerate(zip(a,b)) for d in diffs(x,y,path+(n,))]
 return [] if a==b else [{'path':list(path),'before':a,'after':b}]
changes=diffs(old,new)
assert changes==cmp['location_leaf_changes'] and len(changes)==27
assert all(len(r['path'])==5 and r['path'][0]=='statements' and r['path'][2] in ('exact_companions','related_theorems') and r['path'][-1]=='line' for r in changes)
reconstructed=copy.deepcopy(raw);permutations=[];occurrences=0;duplicate_occurrences=0
for i,(before,generated,normalized) in enumerate(zip(old['statements'],raw['statements'],new['statements'])):
 for collection in ('exact_companions','related_theorems'):
  old_entries=before[collection];raw_entries=generated[collection];new_entries=normalized[collection]
  assert Counter(map(canonical,raw_entries))==Counter(map(canonical,new_entries))
  assert len(old_entries)==len(raw_entries)==len(new_entries)
  # Independently match each occurrence by all stable fields, retaining duplicate multiplicity.
  positions=defaultdict(deque)
  for j,entry in enumerate(raw_entries):
   assert list(entry)==['name','file','line']
   positions[(entry['name'],entry['file'])].append(j)
  order=[]
  for entry in old_entries:
   key=(entry['name'],entry['file']);assert positions[key]
   order.append(positions[key].popleft())
  assert all(not q for q in positions.values()) and sorted(order)==list(range(len(raw_entries)))
  ordered=[raw_entries[j] for j in order]
  assert ordered==new_entries
  reconstructed['statements'][i][collection]=ordered
  if order!=list(range(len(order))):permutations.append({'path':['statements',i,collection],'raw_indices_in_baseline_order':order,'occurrence_count':len(order),'explicit_mapping':False})
  occurrences+=len(new_entries)
  duplicate_occurrences+=sum(n-1 for n in Counter(map(canonical,new_entries)).values())
assert reconstructed==new and permutations==cmp['whole_object_permutations'] and len(permutations)==4
assert occurrences==cmp['companion_occurrences']==544
exact=sum(len(r['exact_companions']) for r in new['statements']);related=sum(len(r['related_theorems']) for r in new['statements'])
assert (exact,related)==(131,413)
source_pins={};contents={};locations=[]
def content(entry,name,kind):
 p=ROOT/entry['file']
 assert p.resolve().parent==(ROOT/'Combinatorics/Ramsey/Lean/GowersSzemeredi').resolve()
 if p not in contents:contents[p]=p.read_text();source_pins[str(p)]=sha(p)
 lines=contents[p].splitlines();line=entry['line'];assert type(line) is int and 1<=line<=len(lines)
 tail='\n'.join(lines[line-1:])
 locations.append({'name':name,'file':entry['file'],'line':line,'kind':kind})
 return tail
alias=None
for row in new['statements']:
 name=row['statement'];text=content(row,name,'catalogue_prop')
 assert re.match(r'^def '+re.escape(name)+r'\s*:\s*Prop\s*:=',text),row
 for collection in ('exact_companions','related_theorems'):
  for entry in row[collection]:
   assert re.fullmatch(re.escape(name)+r'_\w+',entry['name'])
   text=content(entry,entry['name'],collection)
   if entry['name']=='corollary_15_2_of_general':
    assert collection=='exact_companions' and name=='corollary_15_2'
    assert entry=={'name':'corollary_15_2_of_general','file':'Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs15WalshGeneral.lean','line':288}
    assert text.startswith('alias corollary_15_2_of_general := corollary_15_2_holds\n')
    targets=[e for e in row['exact_companions'] if e['name']=='corollary_15_2_holds']
    assert len(targets)==1 and targets[0]=={'name':'corollary_15_2_holds','file':'Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs15Walsh2.lean','line':45}
    target_text=(ROOT/targets[0]['file']).read_text().splitlines()[44]
    assert target_text=='theorem corollary_15_2_holds : corollary_15_2 := by'
    assert (ROOT/entry['file']).read_text().splitlines()[0]=='import GowersSzemeredi.Proofs15Walsh2'
    alias={'entry':entry,'target':targets[0],'alias_and_target_source_lines_exact':True,'direct_target_module_import_present':True}
    continue
   match=re.match(r'^theorem '+re.escape(entry['name'])+r'\b',text);assert match,entry
   header=text[match.end():].split(':=',1)[0]
   is_exact=re.fullmatch(r'\s*:\s*'+re.escape(name)+r'\s*',header) is not None
   assert is_exact==(collection=='exact_companions'),entry
assert len(locations)==664 and len(source_pins)==288 and source_pins==cmp['source_location_pins']
assert alias is not None
for path,h in source_pins.items():assert sha(path)==h,path
for path,h in pins.items():assert sha(path)==h,path
write('locations.json',{'locations':locations,'source_pins':source_pins,'walsh_alias':alias})
write('report.json',{'status':'PASS actual post04fd source inventory only; no new merged native outcome asserted','recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_parent':gen['base_commit'],'incoming_merge_head':gen['merge_head'],'current_inventory_sha256':sha(inventory),'generator_actual_evidence':{'receipt':{'path':str(INP/'generator-receipt.json'),'sha256':sha(INP/'generator-receipt.json')},'terminal_exit':0,'stderr_empty':True,'generator_hash_unchanged':True,'started_at':gen['started_at'],'finished_at':gen['finished_at']},'comparison':{'path':str(INP/'comparison.json'),'sha256':sha(INP/'comparison.json')},'ordered_rows':120,'whole_companion_occurrences':544,'exact_companion_occurrences':exact,'related_theorem_occurrences':related,'duplicate_identical_occurrences_beyond_first':duplicate_occurrences,'whole_object_permutations':permutations,'line_only_leaf_changes':changes,'all_other_values_keys_order_and_qualifications_identical_to_baseline':True,'all_raw_objects_and_duplicate_multiplicities_preserved':True,'normalized_bytes_equal_current_repository_inventory':True,'source_location_checks':{'catalogue_props':120,'companion_occurrences':544,'total':664,'unique_source_files':288,'source_pins_equal_comparison':True,'all_exact_vs_related_classifications_match_source':True,'walsh_alias':alias},'findings':[],'limitations':['Read-only inventory/source review, new /tmp report files only. No native/Lean/generator/comparator/helper execution, tests, Git command, repository/cache mutation or source composition.','Receipt proves actual inventory generator exit0 only. It is not native elaboration evidence for the new merged source.','All ordered statuses and paper-fidelity qualifications are preserved; catalogue coverage is not proof of fidelity to every printed claim.','Current source positions are checked against the stable working tree and comparison pins; no claim of an already-created merge commit.'],'input_pins':pins,'review_script':{'path':str(OUT/'review.py'),'sha256':sha(OUT/'review.py')}})
write('freeze.json',{'status':'Frozen independent post04fd source inventory review','assets':[{'path':str(OUT/n),'sha256':sha(OUT/n)} for n in ('review.py','report.json','locations.json')]})
(OUT/'review.py').chmod(0o444)
print(json.dumps({'status':'PASS','report_sha256':sha(OUT/'report.json'),'freeze_sha256':sha(OUT/'freeze.json'),'location_file_sha256':sha(OUT/'locations.json')},indent=2))
