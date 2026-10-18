"""Independent static review only: no supplied generator, guard, runner, or compiler execution."""
from pathlib import Path
import ast,collections,hashlib,json,re
B=Path('/tmp/zfc-prefix246-lean/coverage');R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
M=B/'guards-four/pipeline-manifest.json';P=B/'plan-four/generation.json';U=B/'grouped-four-reuse-014.json';N=B/'grouped-four-next020-selection.json'
assert sha(M)=='9ee21ec2c106e88f01b1613588dc65b0cdd1f12e04abcd13abc8fbaabb151b09'
assert sha(P)=='174870fefd527465036748bd5649f9acde8dcfad3a46e8ee33884c888507e223'
assert sha(U)=='d2494cb13f4a883ae55bafbbdae4300b8a923f8eb899757bdcb56a7488a73251'
assert sha(N)=='68d9935f7e25031358df63bfc4c53e966128866334c709c0ab8844dd02bf3b11'
m=json.loads(M.read_text());p=json.loads(P.read_text());units={u['module']:u for u in m['units']};plan={u['module']:u for u in p['units']};cuts=p['cut_frontier'];joins=p['join_plan']
known={json.loads(Path(x).read_text())['fresh_modules'][0]['module'] for x in json.loads(U.read_text())};selected20=json.loads(N.read_text())['modules'];assert len(known)==14 and len(selected20)==20 and not known.intersection(selected20)
prior=known|set(selected20);remaining=[u for u in m['units'] if u['module'] not in prior];assert len(remaining)==68
assert collections.Counter(x['kind'] for x in remaining)=={'closed_cuts':52,'binary_composition':15,'closed_final':1}
# Parse the actual Lean literal independently without importing the generator.
tp=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ActualTree254.lean';assert sha(tp)==p['tree_source_sha256']
raw=tp.read_text().split('def tree : Tree :=',1)[1].split('theorem tree_eq',1)[0]
pat=re.compile(r'\s*(\.[A-Za-z]+|[()]|[0-9]+)');tokens=[];i=0
while raw[i:].strip():
 z=pat.match(raw,i);assert z;tokens.append(z[1]);i=z.end()
it=iter(tokens)
def edge(t=None):
 t=next(it) if t is None else t
 if t=='(':
  x=edge();assert next(it)==')';return x
 assert t in ['.inc','.decnz','.brk','.cont','.halt'];return (t,0 if t=='.halt' else int(next(it)))
def tree(t=None):
 t=next(it) if t is None else t
 if t=='(':
  x=tree();assert next(it)==')';return x
 if t=='.node':return ('N',tree(),tree())
 assert t=='.leaf';return ('L',edge())
t=tree();assert next(it,None) is None
nodes={}
def visit(t,path):
 if t[0]=='L':v=(0,1,2 if t[1][0]=='.decnz' else 1,0)
 else:
  a=visit(t[1],path+(False,));b=visit(t[2],path+(True,));v=(1+a[0]+b[0],a[1]+b[1],a[2]+b[2],1+max(a[3],b[3]))
 nodes[path]=(t,v);return v
assert visit(t,())==(6459,6460,8391,34)
for c in cuts:
 path=tuple(c['path']);v=nodes[path][1];assert v==(c['nodes'],c['leaves'],c['guards'],c['depth']);assert v[2]<=64
assert len(cuts)==233 and len({tuple(c['path']) for c in cuts})==233
assert sum(c['leaves'] for c in cuts)==6460 and sum(c['guards'] for c in cuts)==8391
for a in cuts:
 for b in cuts:
  if a['index']!=b['index']:assert a['path']!=b['path'][:len(a['path'])]
def endpoint(ref):return (cuts if ref[0]=='cut' else joins)[ref[1]]
for j,q in enumerate(joins):
 assert q['index']==j and q['theorem']=='join_'+str(j) and nodes[tuple(q['path'])][0][0]=='N'
 for bit,side in [(False,'left'),(True,'right')]:
  e=endpoint(q[side]);assert e['path']==q['path']+[bit]
  if q[side][0]=='join':assert q[side][1]<j
assert len(joins)==232 and joins[-1]['path']==[]
# Every actual branch belongs to the unique composed frontier.
visitedcuts=[];visitedjoins=[]
def compose(ref):
 kind,j=ref
 if kind=='cut':visitedcuts.append(j);return
 visitedjoins.append(j);compose(joins[j]['left']);compose(joins[j]['right'])
compose(('join',231));assert sorted(visitedcuts)==list(range(233)) and sorted(visitedjoins)==list(range(232))
NS='SetTheory.BusyBeaver.ZFC.SitesPrefix246';base=units['BusyBeaver.ZFC.SitesPrefix246Batch011']
base_source=Path(base['source_path']).read_text();doc=base_source[base_source.index('\n/-!'):base_source.index('/-- Cut')];footer='\nend '+NS+'\n'
def bits(xs):return '['+', '.join('true' if x else 'false' for x in xs)+']'
def goal(xs):return 'allSites SitePrefix246.checkSite '+bits(xs[::-1])+'\n      (descend ActualTree254.tree '+bits(xs)+') = true'
def header(imports):return ''.join('import '+x+'\n' for x in imports)+doc
def audit(u,goals):return 'import '+u['module']+'\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen RegisterPath RMBisim SiteCoverage SitesPrefix246\n\n'+''.join('#print axioms '+NS+'.'+x+'\n' for x in u['probe_names'])+''.join('\nexample : '+g+' := '+n+'\n' for n,g in zip(u['probe_names'],goals))
def normalize_guard(u):
 tr=ast.parse(Path(u['guard']).read_text());found=set()
 metadata={'MODULE':u['module'],'SOURCE_SHA':u['source_sha256'],'AUDIT_SHA':u['audit_sha256'],'PROBES':u['probe_names'],'CALLERS':u['callers'],'DEPENDENCY_PINS':{x:{'source_sha256':units[x]['source_sha256'],'audit_sha256':units[x]['audit_sha256']} for x in u['generated_direct_dependencies']}}
 for node in tr.body:
  if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
   key=node.targets[0].id
   if key in metadata:
    assert ast.literal_eval(node.value)==metadata[key],(u['module'],key);node.value=ast.Constant(value='UNIT_METADATA_'+key);found.add(key)
   elif key in ['S','A']:
    v='source' if key=='S' else 'audit';want=ast.parse(key+'=a.'+v+'.resolve() if a.'+v+' else Path('+repr(u[v+'_path'])+')').body[0];assert ast.dump(node)==ast.dump(want);node.value=ast.Constant(value='UNIT_PATH_'+key);found.add(key)
   elif key=='r':
    kws=[k for k in node.value.keywords if k.arg=='project_module_count'];assert len(kws)==1 and ast.literal_eval(kws[0].value)==u['expected_provider_count'];kws[0].value=ast.Constant(value='UNIT_PROVIDER_COUNT');found.add('record_count')
  elif isinstance(node,ast.Assert):
   if ast.unparse(node.test).startswith('imports(S) =='):
    assert ast.literal_eval(node.test.comparators[0])==u['imports'];node.test.comparators[0]=ast.Constant(value='UNIT_IMPORTS');found.add('imports')
   elif ast.unparse(node.test).startswith('set(closure) == set(selected) and len(closure) =='):
    count=node.test.values[1];assert ast.literal_eval(count.comparators[0])==u['expected_provider_count'];count.comparators[0]=ast.Constant(value='UNIT_PROVIDER_COUNT');found.add('closure_count')
 assert found==set(metadata)|{'S','A','record_count','imports','closure_count'},found
 assert isinstance(tr.body[0],ast.Expr);tr.body[0].value=ast.Constant(value='UNIT_DOCSTRING')
 return ast.dump(tr,include_attributes=False)
normalized=normalize_guard(base);allcutids=[];alljoinids=[];selection=[];seen=set();closures={}
for u in m['units']:
 for k,v in plan[u['module']].items():assert u[k]==v
 for pk,hk in [('source_path','source_sha256'),('audit_path','audit_sha256'),('guard','guard_sha256')]:assert sha(u[pk])==u[hk]
 actualimports=re.findall(r'^import (\S+)$',Path(u['source_path']).read_text(),re.M);assert actualimports==u['imports']
 direct=[x for x in actualimports if x in units];assert direct==u['generated_direct_dependencies'] and set(direct)<=seen
 closure=set(direct)
 for x in direct:closure.update(closures[x])
 assert sorted(closure)==u['generated_transitive_dependencies'];assert u['expected_provider_count']==24+len(closure);closures[u['module']]=closure;seen.add(u['module'])
 if u['module'] in prior:continue
 assert normalize_guard(u)==normalized,('guard logic differs',u['module'])
 s=header(u['imports']);goals=[]
 if u['kind']=='closed_cuts':
  assert not direct and len(u['cuts'])<=4 and u['probes']==u['callers']==len(u['cuts'])
  assert u['guards']==sum(cuts[i]['guards'] for i in u['cuts'])<=128 and u['leaves']==sum(cuts[i]['leaves'] for i in u['cuts'])
  for i in u['cuts']:
   c=cuts[i];g=goal(c['path']);s+=f"/-- Cut {i}: {c['leaves']} leaves, {c['guards']} guards. -/\ntheorem block_{i} :\n    {g} := by decide +kernel\n\n";goals.append(g);allcutids.append(i)
  assert u['probe_names']==['block_'+str(i) for i in u['cuts']]
 elif u['kind']=='binary_composition':
  js=[q for q in joins if 'BusyBeaver.ZFC.'+q['module']==u['module']];assert len(js)==u['join_count']<=16 and u['probes']==u['callers']==len(js)
  expected_imports=list(dict.fromkeys(['BusyBeaver.ZFC.'+x for x in ['ActualTree254','SiteCoverage','SitePrefix246']]+['BusyBeaver.ZFC.'+endpoint(q[side])['module'] for q in js for side in ['left','right'] if 'BusyBeaver.ZFC.'+endpoint(q[side])['module']!=u['module']]))
  assert expected_imports==u['imports']
  for q in js:
   x=q['path'];g=goal(x);s+=f"theorem {q['theorem']} :\n    {g} :=\n  allSites_join SitePrefix246.checkSite {bits(x[::-1])}\n    (descend ActualTree254.tree {bits(x+[False])})\n    (descend ActualTree254.tree {bits(x+[True])})\n    {endpoint(q['left'])['theorem']} {endpoint(q['right'])['theorem']}\n\n";goals.append(g);alljoinids.append(q['index'])
  assert u['probe_names']==[q['theorem'] for q in js]
 else:
  assert u['kind']=='closed_final' and u['probes']==u['callers']==3 and u['probe_names']==['all_sites','actual_walk_checked','actual_walk_exists']
  # Entire final source/audit are manually read and pinned; verify the exact generic APIs.
  src=Path(u['source_path']).read_text();aud=Path(u['audit_path']).read_text()
  assert '  join_231\n' in src and src.count('theorem ')==3
  assert 'SitePrefix246.checkSite (consume P d) e = true' in src
  assert '    ActualTree254.tree_eq all_sites P e d hw' in src and '    ActualTree254.tree_eq all_sites P\n' in src
  assert 'theorem actual_walk_exists (P : List Bool)' in src and 'theorem actual_walk_checked (P : List Bool)' in src
  assert re.findall(r'^#print axioms (\S+)$',aud,re.M)==[NS+'.'+q for q in u['probe_names']] and len(re.findall(r'^example\b',aud,re.M))==3
 if u['kind']!='closed_final':
  assert Path(u['source_path']).read_text()==s+footer,('source differs',u['module'])
  assert Path(u['audit_path']).read_text()==audit(u,goals),('audit differs',u['module'])
 selection.append(u)
assert allcutids==[i for i in range(98,233) if i!=210] and alljoinids==list(range(232))
assert len(closures['BusyBeaver.ZFC.SitesPrefix246'])==101 and set(closures['BusyBeaver.ZFC.SitesPrefix246'])==set(units)-{'BusyBeaver.ZFC.SitesPrefix246'}
# Recheck the existing common source/provider identities only; no future PASS claimed.
site_path=Path(m['site_evidence']);assert sha(site_path)==m['site_evidence_sha256'];site=json.loads(site_path.read_text());assert site['status']=='PASS' and site['before']==site['after'];refs=0
for path,h in site['before'].items():assert sha(path)==h;refs+=1
for q in site['actual_first_providers']:assert Path(q['actual_first']).resolve()==Path(q['resolved']).resolve() and sha(q['actual_first'])==q['sha256']
read_paths=[tp,R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SiteCoverage.lean',R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SitePrefix246.lean',B/'generate_sites_prefix246.py',B/'run_pipeline.py']
record={'status':'SOURCE_ONLY_REMAINING68_REVIEW_PASS_NOT_EXECUTED','reviewer':'/root/opening_encoder','manifest':{'path':str(M),'sha256':sha(M)},'plan':{'path':str(P),'sha256':sha(P)},'already_passed_reuse_list':{'path':str(U),'sha256':sha(U)},'excluded_next20_selection':{'path':str(N),'sha256':sha(N),'status':'Selection excluded; no execution result inferred in this review'},'read_source_bindings':[{'path':str(x),'sha256':sha(x)}for x in read_paths],'site_parent':{'path':str(site_path),'sha256':sha(site_path),'current_input_references_rechecked':refs},'selected_units':selection,'checks':{'remaining_units':68,'remaining_closed_cut_units':52,'remaining_cut_theorems':len(allcutids),'remaining_cut_guard_cases':sum(cuts[i]['guards']for i in allcutids),'remaining_cut_leaves':sum(cuts[i]['leaves']for i in allcutids),'join_modules':15,'join_theorems':232,'final_modules':1,'final_probes':3,'final_callers':3,'whole_frontier_cuts':233,'whole_tree_nodes':6459,'whole_tree_leaves':6460,'whole_tree_guard_cases':8391,'independent_literal_tree_parse':True,'prefix_free_frontier':True,'both_child_path_and_theorem_arguments_checked':True,'root_composition_reaches_every_cut_once':True,'whole_cut_and_join_sources_audits_reconstructed_byte_exact':True,'final_source_audit_read_complete_and_pinned':True,'all68_guard_ASTs_equal_checked_cut_logic_modulo_validated_metadata':True,'all102_source_audit_guard_hashes_and_dependency_closures_checked':True,'final_generated_ancestor_modules':101,'final_project_provider_count':125},'mathematical_scope':{'arbitrary_PC':'For every P : List Bool, actual_walk_exists gives a decoder leaf. For every returned edge/depth, actual_walk_checked gives checkSite on consume P d, retaining zero extension/truncation. No clean-PC or standard-path hypothesis.','joins':'allSites_join takes both false::revPrefix and true::revPrefix hypotheses. Every join uses the actual two descend subtrees and separately proved child theorems. The final join_231 is the empty-prefix actual root.','runtime':'These are Boolean coverage proofs. Their unbounded operation meaning comes from checked SitePrefix246 soundness plus frame assumptions; no whole-run or PA consistency theorem is claimed here.','limits':'New sources/audits introduce no enlarged proof limits; reused SiteCoverage has historical options already present in its pinned checked boundary.'},'execution_here':{'generator':False,'guard':False,'runner':False,'compiler':False,'version_query':False},'findings':[]}
review=B/'grouped-four-remaining068-source-review.json';review.write_text(json.dumps(record,indent=2)+'\n');out=B/'grouped-four-remaining068-selection.json';out.write_text(json.dumps({'manifest_sha256':sha(M),'excluded_reuse_list_sha256':sha(U),'excluded_next20_selection_sha256':sha(N),'review_sha256':sha(review),'modules':[u['module']for u in selection],'units':selection},indent=2)+'\n')
print(json.dumps({'review':str(review),'review_sha256':sha(review),'selection':str(out),'selection_sha256':sha(out),'checks':record['checks']},indent=2))
