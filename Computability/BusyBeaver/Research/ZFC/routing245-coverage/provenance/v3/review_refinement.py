"""Independent source/data/metadata review only; no delivered program is executed."""
from pathlib import Path
import ast,hashlib,json,re
B=Path('/tmp/zfc-routing245-lean/coverage-production/v3');V=B.parent/'v2';D=B/'sources';N='SetTheory.BusyBeaver.ZFC.SitesRouting245';checks=0;pins={}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ck(v,m='review mismatch'):
 global checks
 assert v,m;checks+=1
def pin(p,h):
 p=Path(p);ck(sha(p)==h,str(p));pins[str(p)]=h
norm=lambda s:re.sub(r'\s+','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
bits=lambda p:'['+', '.join('true'if x=='1'else'false'for x in p)+']'
goal=lambda p:f'allSites SiteRouting245.checkSite {bits(p[::-1])} (descend TreeRouting245.tree {bits(p)}) = true'
pin(V/'independent-generated-family-review.json','99afd460296772c69441157d27ff09731ed9edcf995dd095d12a6e0c01de986c')
prior=json.loads((V/'independent-generated-family-review.json').read_text())
for p,h in prior['current_pins'].items():pin(p,h)
pin(D/'generation.json','ca70be3402b6a0b1c33708970ac6400bcba7843382dd43e77fe09c9523e7db6b')
old=json.loads((V/'sources/generation.json').read_text());g=json.loads((D/'generation.json').read_text())
inv=json.loads((B/'static-plan-inventory.json').read_text())
for q in inv['preserved_files']+list(inv['source_programs'].values())+[inv['guard_delta']]:pin(q['path'],q['sha256'])
for q in g['inputs']+[g['generator']]:pin(q['path'],q['sha256'])
# Reconstruct the original exact DAG's ordered paths, rather than trust the report's child census.
program=next(Path(q['path'])for q in g['inputs']if q['path'].endswith('/ProgramRouting245.lean'))
pat=r'^private def row(\d{3}) : Row := \((\(\.[a-z]+ \d+\)|\.halt), (\(\.[a-z]+ \d+\)|\.halt)\)$'
rows={int(m[1]):(m[2],m[3])for m in re.finditer(pat,program.read_text(),re.M)};ck(set(rows)==set(range(203)));leaves=[]
def walk(n,p):
 for bit,s in zip('01',rows[n]):
  t=s.strip('()').removeprefix('.').split();k=t[0];v=int(t[1])if len(t)>1 else None
  if k=='node':ck(0<=v<n);walk(v,p+bit)
  else:ck(k in ['inc','decnz','brk','cont','halt']);leaves.append((p+bit,k,v))
walk(202,'');ck(len(leaves)==6460 and sum(2 if k=='decnz'else 1 for p,k,v in leaves)==8391)
p=old['cut_frontier'][42]['path'];children=g['refinement']['children'];ck(g['cut_frontier']==old['cut_frontier']and g['join_plan']==old['join_plan'])
for c,side,want in zip(children,'01',[(970,990,20,26),(990,1017,27,35)]):
 xs=[(i,k)for i,(q,k,v)in enumerate(leaves)if q.startswith(p+side)]
 ck(c['path']==p+side and (xs[0][0],xs[-1][0]+1,len(xs),sum(2 if k=='decnz'else 1 for i,k in xs))==want)
 ck((c['lo'],c['hi'],c['leaves'],c['guards'])==want)
ck(g['units'][3:]==old['units'][2:]);ck(g['reused_units'][:-1]==old['reused_units']);ck(len(g['units'])==209 and len(g['reused_units'])==17)
for u in g['units']:
 for role in ['source','audit']:pin(D/u[role],u[role+'_sha256'])
for u in g['units'][3:]:
 for role in ['source','audit']:ck((D/u[role]).read_bytes()==(V/'sources'/u[role]).read_bytes())
base=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SiteRouting245']
header=lambda im:'\n'.join('import '+m for m in im)+'\nnamespace '+N+'\nopen RegisterPath RMBisim SiteCoverage\n'
footer='\nend '+N
for u,c in zip(g['units'][:2],children):
 name=c['theorem'].rsplit('.',1)[-1]
 ck(u['imports']==base and u['probe_names']==[name] and u['probes']==u['callers']==1)
 ck(norm((D/u['source']).read_text())==norm(header(base)+f'theorem {name} : {goal(c["path"])} := by decide +kernel'+footer))
 au='import '+u['module']+'\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen RegisterPath RMBisim SiteCoverage SitesRouting245\n#print axioms '+N+'.'+name+'\nexample : '+goal(c['path'])+' := '+name
 ck(norm((D/u['audit']).read_text())==norm(au))
u=g['units'][2];extra=['BusyBeaver.ZFC.'+c['module']for c in children];ck(u['imports']==base+extra)
body=f'theorem block_42 : {goal(p)} := allSites_join SiteRouting245.checkSite {bits(p[::-1])} (descend TreeRouting245.tree {bits(p+"0")}) (descend TreeRouting245.tree {bits(p+"1")}) '+children[0]['theorem']+' '+children[1]['theorem']
ck(norm((D/u['source']).read_text())==norm(header(base+extra)+body+footer));ck((D/u['audit']).read_bytes()==(V/'sources'/old['units'][0]['audit']).read_bytes())
ck(sum(u['probes']for u in g['units'])==sum(u['callers']for u in g['units'])==431)
ck(sum(u['probes']for u in g['reused_units'])==45 and sum(u['callers']for u in g['reused_units'])==48)
ck((g['complete_probes'],g['complete_callers'],g['effective_frontier_cuts'],g['effective_binary_joins'])==(476,479,237,236))
# Normal production reuse of cut43 retains preparation, raw reports and first-object checks.
r=g['reused_units'][-1];ck(r['origin']=='v2_single_cut'and r['cuts']==[43]);pin(r['record']['path'],'4ae32a10f2da423204bc04b50a8609f9a6fc2495cb99831135c53496af1aafc7');d=json.loads(Path(r['record']['path']).read_text())
ck(d['status']=='PASS'and d['before']==d['after']and not d['prepare_only']and (d['named_axiom_probes'],d['callers'])==(1,1))
for flag in ['all_input_provider_postchecks','only_standard_axioms','source_object_recorded_before_audit','all_fresh_objects_unchanged_after_audit']:ck(d[flag])
for p0,h in d['before'].items():pin(p0,h)
for role in ['source','audit']:
 q=d[role];pin(q['path'],q['sha256']);pin(q['snapshot'],q['sha256']);ck(q['sha256']==r[role]['sha256'])
f,=d['fresh_modules'];pin(f['path'],f['sha256']);ck(f['sha256']==r['fresh_object']['sha256']and all(f[k]==d['source_pass_object'][k]for k in ['module','path','sha256','source_sha256']))
for c in d['commands']:ck(Path(c['log']).read_text()==c['output']and c['exit_code']==0 and not c['timed_out'])
ck([c['label']for c in d['commands']]==['source','audit']);ck(d['actual_axiom_sets']==[{'name':N+'.block_43','axioms':['propext','Quot.sound']}])
prep=d['preparation'];pin(prep['path'],prep['sha256']);pd=json.loads(Path(prep['path']).read_text());ck(pd['status']=='PREPARED_NOT_BUILT'and pd['commands']==[]and pd['fresh_modules']==[])
# Entire proof launcher, provider logic and successful-receipt validator unchanged at AST level.
funcs=lambda p:{x.name:ast.dump(x,include_attributes=False)for x in ast.parse(Path(p).read_text()).body if isinstance(x,(ast.FunctionDef,ast.AsyncFunctionDef))}
a,b=funcs(V/'check-production-v2.py'),funcs(B/'check-production-v3.template.py');ck(a.keys()==b.keys())
for n in a:
 if n!='main':ck(a[n]==b[n],'guard function '+n)
manifest_sha=sha(D/'generation.json');template=(B/'check-production-v3.template.py').read_text()
want=template.replace('MANIFEST_SHA=None  # Pin after root emits and reviews the refined source manifest.','MANIFEST_SHA='+repr(manifest_sha)).replace("default=HERE/'sources/generation.json'",'default=Path('+repr(str(D/'generation.json'))+')')
ck((B/'check-production-v3.py').read_text()==want);pin(B/'check-production-v3.py',sha(B/'check-production-v3.py'))
pp=B/'prepared-left/unit000/verification.json';pd=json.loads(pp.read_text());pin(pp,sha(pp))
ck(pd['status']=='PREPARED_NOT_BUILT'and pd['prepare_only']and pd['commands']==[]and pd['fresh_modules']==[]and pd['before']==pd['after']and pd['all_input_provider_postchecks'])
ck(pd['project_module_count']==23 and pd['expected_named_axiom_probes']==pd['expected_callers']==1 and pd['module']==g['units'][0]['module'])
for p0,h in pd['before'].items():pin(p0,h)
for role in ['source','audit']:
 q=pd[role];pin(q['path'],q['sha256']);pin(q['snapshot'],q['sha256']);ck(q['sha256']==g['units'][0][role+'_sha256'])
for q in pd['reused_modules']:
 a=next(x for x in pd['actual_first_providers']if x['module']==q['module']);ck(Path(a['actual_first']).resolve()==Path(q['object']).resolve()and a['sha256']==q['object_sha256'])
out=dict(status='CLEAN_REFINEMENT_SOURCE_GENERATED_FAMILY_AND_PREPARATION_REVIEW',findings=[],checks=checks,reviewer_script_sha256=sha(__file__),generation=dict(path=str(D/'generation.json'),sha256=manifest_sha),guard=dict(path=str(B/'check-production-v3.py'),sha256=sha(B/'check-production-v3.py')),prepared=dict(path=str(pp),sha256=sha(pp),inputs=len(pd['before']),projects=23),prior_v2_review=prior['generation'],reused_cut43=r['record'],current_pins=pins,census=dict(new_modules=209,reused_modules=17,new_probes=431,new_callers=431,complete_probes=476,complete_callers=479,prospective_final_projects=248),semantics='Actual203-row DAG expanded; both actual children exactly partition cut42; full three new sources/audits reconstructed; every other scheduled v2 byte unchanged; block42 statement and final arbitrary-PC statement preserved. Full v2 provider/launcher validator function AST unchanged.',limitations=['Source/generated/preparation review only: no v3 actual proof result is claimed here.','The successful cut43 record is existing evidence, not replayed.','Complete coverage and external BinaryRouting245 remain dependent on all required actual successful modules.','No compiler/guard/emitter/freezer/version query, simulation or maintained edit was performed.'])
p=B/'independent-refinement-review.json';ck(not p.exists());p.write_text(json.dumps(out,indent=2)+'\n');print(p,sha(p),checks)
