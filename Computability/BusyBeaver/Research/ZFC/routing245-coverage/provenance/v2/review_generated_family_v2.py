"""Independent static reconstruction of the emitted routing245 coverage family.
No delivered emitter, proof guard, symbolic simulator or compiler is invoked.
"""
from pathlib import Path
import hashlib,json,re
B=Path('/tmp/zfc-routing245-lean/coverage-production/v2');D=B/'sources';G=json.loads((D/'generation.json').read_text());NS='SetTheory.BusyBeaver.ZFC.SitesRouting245';pins={};checks=0
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ck(v,m='static mismatch'):
 global checks
 assert v,m;checks+=1
def pin(p,h):ck(sha(p)==h,str(p));pins[str(p)]=h
norm=lambda s:re.sub(r'\s+','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
bits=lambda p:'['+', '.join('true'if x=='1'else'false'for x in p)+']'
goal=lambda p:f'allSites SiteRouting245.checkSite {bits(p[::-1])} (descend TreeRouting245.tree {bits(p)}) = true'
pin(D/'generation.json','70a67b42ca63d8c363e7e100e3621ee5c332fa7c50c4735dbce3d61cb316ac48')
for q in [G['generator']]+G['inputs']:pin(q['path'],q['sha256'])
program=next(q for q in G['inputs']if q['path'].endswith('/ProgramRouting245.lean'));s=Path(program['path']).read_text()
pat=r'^private def row(\d{3}) : Row := \((\(\.[a-z]+ \d+\)|\.halt), (\(\.[a-z]+ \d+\)|\.halt)\)$'
rows={int(m[1]):(m[2],m[3])for m in re.finditer(pat,s,re.M)};ck(set(rows)==set(range(203)));leaves=[]
def walk(n,p):
 for b,s in zip('01',rows[n]):
  t=s.strip('()').removeprefix('.').split();k=t[0];v=int(t[1])if len(t)>1 else None
  if k=='node':ck(0<=v<n);walk(v,p+b)
  else:ck(k in ['inc','decnz','brk','cont','halt']);leaves.append((p+b,k,v))
walk(202,'');ck(len(leaves)==6460)
plain=next(q for q in G['inputs']if q['path'].endswith('sites_logical.json'));kinds={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'}
ck([[p,kinds[k],a]for p,k,a in leaves]==json.loads(Path(plain['path']).read_text()))
leaf={p:(i,k,a)for i,(p,k,a)in enumerate(leaves)};meta={}
def measure(p):
 if p in leaf:
  i,k,a=leaf[p];v=dict(lo=i,hi=i+1,leaves=1,guards=2 if k=='decnz'else 1,nodes=0,height=0)
 else:
  l,r=measure(p+'0'),measure(p+'1');ck(l['hi']==r['lo']);v=dict(lo=l['lo'],hi=r['hi'],leaves=l['leaves']+r['leaves'],guards=l['guards']+r['guards'],nodes=1+l['nodes']+r['nodes'],height=1+max(l['height'],r['height']))
 meta[p]=v;return v
ck(measure('')==dict(lo=0,hi=6460,leaves=6460,guards=8391,nodes=6459,height=51))
cuts=[];joins=[]
def split(p):
 if meta[p]['guards']<=64:
  n=len(cuts);cuts.append(dict(index=n,path=p,**meta[p]));return ['cut',n]
 l,r=split(p+'0'),split(p+'1');n=len(joins);joins.append(dict(index=n,path=p,left=l,right=r));return ['join',n]
ck(split('')==G['root']==['join',234]);ck((len(cuts),len(joins))==(236,235))
for a,b in zip(cuts,G['cut_frontier']):ck(all(b[k]==v for k,v in a.items()))
for a,b in zip(joins,G['join_plan']):ck(all(b[k]==v for k,v in a.items()))
reused={}
for r in G['reused_units']:
 ids=[r['index']]if r['origin']=='pilot'else r['cuts']
 pin(r['record']['path'],r['record']['sha256']);p=Path(r['record']['path']);d=json.loads(p.read_text());ck(d['status']=='PASS'and d['before']==d['after']and d['prepare_only']is False)
 ck((d['named_axiom_probes'],d['callers'])==(r['probes'],r['callers']))
 for f,h in d['before'].items():pin(f,h)
 for key in ['source','audit']:
  q=d[key];pin(q['path'],q['sha256']);pin(q['snapshot'],q['sha256']);ck(q['sha256']==r[key]['sha256'])
 f=d['fresh_modules'][0];ck(len(d['fresh_modules'])==1 and all(f[k]==d['source_pass_object'][k]for k in ['module','path','sha256','source_sha256']));pin(f['path'],f['sha256']);ck(f['sha256']==r['fresh_object']['sha256']and f['source_sha256']==r['source_sha256'])
 for i in ids:
  ck(i not in reused);reused[i]=r;c=G['cut_frontier'][i];ck(c['reused']and c['module']==r['module'])
  name='checked'if r['origin']=='pilot'else 'block_'+str(i)
  ns='SetTheory.BusyBeaver.ZFC.'+r['module']if r['origin']=='pilot'else NS
  ck(c['theorem']==ns+'.'+name)
  st=Path(d['source']['path']).read_text();ck(norm(f'theorem {name} : {goal(c["path"])} := by decide +kernel')in norm(st))
ck(set(reused)==set(range(42))|{70,174}and len(G['reused_units'])==16)
# Reconstruct one remaining cut per module from the unchanged frontier.
batches=[[c['index']]for c in cuts if c['index']not in reused]
ck(len(batches)==192 and len(G['units'])==208)
base=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SiteRouting245'];seen={r['full_module']for r in reused.values()};owned=[]
def endpoint(ref):return (G['cut_frontier']if ref[0]=='cut'else G['join_plan'])[ref[1]]
for u in G['units']:
 pin(D/u['source'],u['source_sha256']);pin(D/u['audit'],u['audit_sha256']);source=(D/u['source']).read_text();audit=(D/u['audit']).read_text();extra=[];body='';names=[];goals=[]
 if u['kind']=='closed_cuts':
  batch_index=int(u['module'][-3:]);ck(u['cuts']==[batch_index]and batch_index not in reused);owned+=u['cuts']
  for i in u['cuts']:
   c=cuts[i];n=f'block_{i}';names.append(n);goals.append(goal(c['path']));body+=f'theorem {n} : {goals[-1]} := by decide +kernel\n';ck(G['cut_frontier'][i]['module']==u['module'].split('.')[-1])
  ck(u['guards']==sum(cuts[i]['guards']for i in u['cuts'])and u['leaves']==sum(cuts[i]['leaves']for i in u['cuts']))
 elif u['kind']=='binary_composition':
  k=int(u['module'][-3:]);ck(u['join_indices']==list(range(16*k,min(16*k+16,235))))
  for i in u['join_indices']:
   q=joins[i];p=q['path'];l,r=endpoint(q['left']),endpoint(q['right']);ck(l['path']==p+'0'and r['path']==p+'1')
   names.append(f'join_{i}');goals.append(goal(p));body+=f'theorem join_{i} : {goal(p)} := allSites_join SiteRouting245.checkSite {bits(p[::-1])} (descend TreeRouting245.tree {bits(p+"0")}) (descend TreeRouting245.tree {bits(p+"1")}) {l["theorem"]} {r["theorem"]}\n'
   for child in [l,r]:
    cm='BusyBeaver.ZFC.'+child['module']
    if cm!=u['module']:ck(cm in seen);extra.append(cm)
    else:ck(child['index']<i)
 else:
  ck(u['kind']=='closed_final'and u['module']=='BusyBeaver.ZFC.SitesRouting245');extra=['BusyBeaver.ZFC.SitesRouting245Join014'];names=['all_sites','actual_walk_checked','actual_walk_exists']
  body='''theorem all_sites : allSites SiteRouting245.checkSite [] TreeRouting245.tree = true := SetTheory.BusyBeaver.ZFC.SitesRouting245.join_234
 theorem actual_walk_checked (P : List Bool) (e : Edge) (d : Nat) (hw : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d)) : SiteRouting245.checkSite (consume P d) e = true := allSites_walk SiteRouting245.checkSite ProgramRouting245.program TreeRouting245.tree TreeRouting245.tree_eq all_sites P e d hw
 theorem actual_walk_exists (P : List Bool) : ∃ e d, walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d) := allSites_walk_total SiteRouting245.checkSite ProgramRouting245.program TreeRouting245.tree TreeRouting245.tree_eq all_sites P'''
 imports=list(dict.fromkeys(base+extra));ck(u['imports']==imports)
 wanted='\n'.join('import '+m for m in imports)+f'\nnamespace {NS}\nopen RegisterPath RMBisim SiteCoverage\n'+body+'\nend '+NS
 ck(norm(source)==norm(wanted),'full source '+u['module']);ck(u['probe_names']==names and u['probes']==len(names))
 au='import '+u['module']+'\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen RegisterPath RMBisim SiteCoverage SitesRouting245\n'+'\n'.join('#print axioms '+NS+'.'+n for n in names)+'\n'
 if u['kind']!='closed_final':au+='\n'.join(f'example : {g} := {n}'for n,g in zip(names,goals))
 else:au+='''example : allSites SiteRouting245.checkSite [] TreeRouting245.tree = true := all_sites
 example (P : List Bool) (e : Edge) (d : Nat) (hw : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d)) : SiteRouting245.checkSite (consume P d) e = true := actual_walk_checked P e d hw
 example (P : List Bool) : ∃ e d, walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d) := actual_walk_exists P'''
 ck(norm(audit)==norm(au),'full audit '+u['module']);ck(len(re.findall(r'^example\b',audit,re.M))==u['callers']==u['probes']);seen.add(u['module'])
ck(sorted(owned)==sorted(set(range(236))-set(reused)))
ck(sum(u['probes']for u in G['units'])==430 and sum(u['callers']for u in G['units'])==430)
ck((G['complete_probes'],G['complete_callers'])==(474,477))
# The successor freezer changes only its manifest digest and default path.
template=B/'check-production-v2.template.py';guard=B/'check-production-v2.py'
pin(template,'eac5b5523594a34633e9e38a9d1e6bebfb1924518294daf2f7209f3390c6e8ed');pin(guard,'ac8761cc41db43183f72846fc6078d943a390c9eec3ab4c0b1d5d37c6bde527c')
want=template.read_text().replace('MANIFEST_SHA=None  # Frozen only after root emits and reviews the exact successor manifest.','MANIFEST_SHA='+repr(sha(D/'generation.json'))).replace("default=HERE/'sources/generation.json'",'default=Path('+repr(str(D/'generation.json'))+')')
ck(guard.read_text()==want)
prep_path=B/'prepared-cut42/unit000/verification.json';prep=json.loads(prep_path.read_text());pin(prep_path,sha(prep_path))
ck(prep['status']=='PREPARED_NOT_BUILT'and prep['prepare_only']and prep['commands']==[]and prep['fresh_modules']==[]and prep['before']==prep['after']and prep['all_input_provider_postchecks'])
ck(prep['module']=='BusyBeaver.ZFC.SitesRouting245Cut042'and prep['cuts']==[42]and prep['project_module_count']==23 and prep['expected_named_axiom_probes']==prep['expected_callers']==1)
for p,h in prep['before'].items():pin(p,h)
for role in ('source','audit'):
 q=prep[role];pin(q['path'],q['sha256']);pin(q['snapshot'],q['sha256']);ck(q['sha256']==G['units'][0][role+'_sha256'])
for q in prep['reused_modules']:
 a=next(x for x in prep['actual_first_providers']if x['module']==q['module']);ck(Path(a['actual_first']).resolve()==Path(q['object']).resolve()and a['sha256']==q['object_sha256'])
output=dict(status='CLEAN_SUCCESSOR_GENERATED_FAMILY_AND_PREPARATION_REVIEW_ONLY',prepared= dict(path=str(prep_path),sha256=sha(prep_path),inputs=len(prep['before']),projects=23,proof_commands=0),exact_guard_freeze_delta=True,findings=[],checks=checks,reviewer_script_sha256=sha(__file__),generation=dict(path=str(D/'generation.json'),sha256=sha(D/'generation.json')),current_pins=pins,census=dict(new_units=208,cut_batches=192,joins_modules=15,final_modules=1,frontier_cuts=236,new_cut_proofs=192,reused_pilot_modules=3,reused_original_modules=13,join_proofs=235,leaves=6460,guards=8391,new_probes=430,new_callers=430,complete_probes=474,complete_callers=477),semantics='Independent actual203-row DAG expansion, exact ordered leaf comparison, all236 prefix cuts, both-child postorder235 joins, full208 source/audit/import patterns, and exact16 existing pilot/original-batch source/object records checked.',limitations=['No generated production proof was executed or claimed by this review.','Actual provider selection and default-limit compilation remain guarded execution obligations.','Final all-sites source closes coverage for arbitrary ProgramRouting245 instruction pointers if every unit passes; it supplies no bootstrap or PA equivalence.'],no_supplied_code_execution=True)
p=B/'independent-generated-family-review.json';ck(not p.exists());p.write_text(json.dumps(output,indent=2)+'\n');print(p,sha(p),checks)
