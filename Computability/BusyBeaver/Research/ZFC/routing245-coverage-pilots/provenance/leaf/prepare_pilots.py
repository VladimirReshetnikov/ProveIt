"""Parse pinned leaf data and emit small source-only coverage measurements.
No supplied program, symbolic executor, checker, compiler, or version query runs.
"""
import collections, hashlib, json, pathlib, re
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs');B=pathlib.Path('/tmp/zfc-routing245-lean/coverage-pilots')
L=R/'Computability/BusyBeaver/Lean';Q=R/'Computability/BusyBeaver/Research/ZFC'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=pathlib.Path(p).stat().st_size)
inp=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-sites_logical.json'
prog=L/'BusyBeaver/ZFC/ProgramRouting245.lean';old=L/'BusyBeaver/ZFC/Prog254.lean'
data=pathlib.Path('/tmp/zfc-routing245-lean/program/generated-v4/program-data.json')
site=pathlib.Path('/tmp/zfc-routing245-lean/site/SiteRouting245.lean')
rec=Q/'results/program-routing245-verification.json'
expected={inp:'f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745',prog:'060a95566e6162b845b3ee734b4134aefeeb3e9c079de705c2d094ca9119ef0b',old:'6e564bd1ba179b2d39fccc3b8c86a681ec0dd6529df9cfa2522500eef140cfde',data:'3beba79cc5d1d7f9e3fae6d18c22115b6ef73c29d5d3e69ba17a460fd4065db3',site:'d05562d7a17c58a45089903977a074ea36559d39a2c5f854d63af5874c951021',rec:'1efd9f64fc8067e85518fc9968752a9a10f78cdeb4f24aa8dd9e8c58d2a53c71'}
for p,h in expected.items():assert sha(p)==h
sites=json.loads(inp.read_text());pd=json.loads(data.read_text())
assert len(sites)==6460 and sites==pd['ordered_sites']
kind={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
def edgeparse(s):
 v=s.strip('()').removeprefix('.').split();return (v[0],int(v[1]) if len(v)>1 else None)
def expand(rows,root):
 out=[]
 def go(i,p):
  for bit,e in zip('01',rows[i]):
   if e[0]=='node':go(e[1],p+bit)
   else:out.append((p+bit,e))
 go(root,'');return out
# Parse exact literal row definitions from the maintained checked source.
rowpat=re.compile(r'^private def row(\d{3}) : Row := \((\(\.[a-z]+ \d+\)|\.halt), (\(\.[a-z]+ \d+\)|\.halt)\)$',re.M)
newrows={int(m[1]):(edgeparse(m[2]),edgeparse(m[3])) for m in rowpat.finditer(prog.read_text())}
assert set(newrows)==set(range(203))
assert all(e[0]!='node' or e[1]<i for i,r in newrows.items() for e in r)
new=expand(newrows,202)
assert new==[(p,(kind[k],a)) for p,k,a in sites]
oldpat=re.compile(r'^  \((\.halt|\.[a-z]+ \d+), (\.halt|\.[a-z]+ \d+)\), -- (\d+)$',re.M)
oldrows={int(m[3]):(edgeparse(m[1]),edgeparse(m[2])) for m in oldpat.finditer(old.read_text())}
assert set(oldrows)==set(range(6459));original=expand(oldrows,0)
assert [e for p,e in original]==[e for p,e in new]
assert sum(p!=q for (p,e),(q,f) in zip(original,new))==6241
assert len(set(p for p,k,a in sites))==6460
assert all(not q.startswith(p) for p,q in zip(sorted(p for p,k,a in sites),sorted(p for p,k,a in sites)[1:]))
# Prefix completeness is independently reconstructed, not inferred from counts.
leafmap={p:(k,a) for p,k,a in sites};prefixes={p[:n] for p in leafmap for n in range(len(p))}
assert all(p not in leafmap and all(p+b in leafmap or p+b in prefixes for b in '01') for p in prefixes)
assert len(prefixes)==6459
zr=lambda p:max(map(len,p.split('1')))
orun=lambda p:max(map(len,p.split('0')))
maxdepth=max(len(p) for p,k,a in sites);maxzero=max(zr(p) for p,k,a in sites);maxone=max(orun(p) for p,k,a in sites)
assert (maxdepth,maxzero,maxone)==(51,6,12)
select=lambda pred,score:max((i for i,r in enumerate(sites) if pred(r)),key=lambda i:(score(sites[i]),-i))
choices=[
 ('deepest_increment',select(lambda r:r[1]=='CI',lambda r:len(r[0]))),
 ('deepest_continue',select(lambda r:r[1]=='CC',lambda r:len(r[0]))),
 ('longest_zero_run',select(lambda r:r[1]=='CD' and zr(r[0])==maxzero,lambda r:len(r[0]))),
 ('deepest_decrement',select(lambda r:r[1]=='CD',lambda r:len(r[0]))),
 ('changed_break',select(lambda r:r[1]=='CB',lambda r:len(r[0]))),
 ('longest_one_run',select(lambda r:orun(r[0])==maxone,lambda r:len(r[0]))),
 ('halt',select(lambda r:r[1]=='CH',lambda r:len(r[0]))),
]
assert [i for label,i in choices]==[1704,1705,1609,1703,1720,4730,6324]
assert len({i for label,i in choices})==7
bits=lambda p:'['+', '.join('true' if b=='1' else 'false' for b in p)+']'
def edgelean(k,a):return '.halt' if k=='CH' else f'.{kind[k]} {a}'
units=[]
for role,i in choices:
 p,k,a=sites[i];op,oe=original[i];assert p!=op or role=='halt'
 m=f'SitesRouting245Pilot{i:04d}';ns=f'SetTheory.BusyBeaver.ZFC.{m}'
 out=B/f'case{i:04d}';out.mkdir();sp=out/(m+'.lean');ap=out/'Audit.lean'
 text=f'''import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteRouting245

/-!
Source-only coverage measurement for exact routed leaf {i}: {role}.
The tree-link theorem and accepted-site theorem use the same literal path
and instruction. SiteRouting245 retains fuel 4000 and margin 64. A decrement
acceptance includes both zero and positive guards. No complete coverage or
concrete-time bound is asserted by this single-site unit.
-/
namespace {ns}
open RegisterPath RMBisim

def path : List Bool := {bits(p)}
def instruction : Edge := {edgelean(k,a)}

/-- Exact leaf/depth of the checked actual routed decoder. -/
theorem actual_leaf : twalk TreeRouting245.tree path 0 = some (instruction, {len(p)}) := by
  decide +kernel

/-- This one actual leaf is accepted at the unchanged certificate fuel. -/
theorem site_checked : SiteRouting245.checkSite path instruction = true := by
  decide +kernel

end {ns}
'''
 au=f'''import BusyBeaver.ZFC.{m}

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim {m}

#print axioms {ns}.actual_leaf
#print axioms {ns}.site_checked

example : twalk TreeRouting245.tree path 0 = some (instruction, {len(p)}) := actual_leaf

example : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1)
    ProgramRouting245.program.root path 0 = some (instruction, {len(p)}) := by
  calc
    _ = twalk TreeRouting245.tree path 0 := by
      simpa only [List.drop_zero] using TreeRouting245.walk_eq_tree path 0
    _ = some (instruction, {len(p)}) := actual_leaf

example : SiteRouting245.checkSite path instruction = true := site_checked
'''
 if k=='CD':
  au+=f'''
example : SiteRouting245.runTo (some (SiteRouting245.physical {a} (by decide), true)) path
    (SiteRouting245.target (breakPath 1 path) (SiteRouting245.allOnes (stripPath false 1 path))
      0 (.plain .unchanged)) = true :=
  (SiteRouting245.check_decnz path {a} (by decide) site_checked).1

example : SiteRouting245.runTo (some (SiteRouting245.physical {a} (by decide), false)) path
    (SiteRouting245.target (incPath path) (SiteRouting245.allOnes path)
      1 (.plain (.decrement (SiteRouting245.physical {a} (by decide))))) = true :=
  (SiteRouting245.check_decnz path {a} (by decide) site_checked).2
'''
 sp.write_text(text);ap.write_text(au)
 units.append(dict(role=role,site_index=i,path=p,depth=len(p),opcode=k,operand=a,edge=[kind[k],a],
                   longest_zero_run=zr(p),longest_one_run=orun(p),old_path_at_same_semantic_ordinal=op,old_depth=len(op),path_changed=(p!=op),
                   guards=2 if k=='CD' else 1,source=desc(sp),audit=desc(ap),module='BusyBeaver.ZFC.'+m,
                   probes=2,callers=5 if k=='CD' else 3,imports=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteRouting245'],status='SOURCE_ONLY_NOT_COMPILED'))
assert sum(x['guards'] for x in units)==9
# Prospective narrow closure: retain reusable generic objects; select the
# already successful new Program object exactly; leave new Site chain null.
bd=json.loads(pathlib.Path('/tmp/zfc-routing245-lean/site/boundary-plan.json').read_text())
providers=[dict(x) for x in bd['providers']]
for x in providers:
 if x['object'] is None:x['status']='OBJECT_NOT_SELECTED_IN_SOURCE_PLAN'
for x in providers:
 if x['module']=='BusyBeaver.ZFC.Routing245Boxes':
  x['source']='/tmp/zfc-routing245-lean/boxes/source-v2/Routing245Boxes.lean';x['source_sha256']=sha(x['source'])
providers.append(dict(module='BusyBeaver.ZFC.SiteRouting245',source=str(site),source_sha256=sha(site),object=None,object_sha256=None,evidence=None,status='OBJECT_NOT_SELECTED_IN_SOURCE_PLAN'))
pr=json.loads(rec.read_text());assert pr['status']=='PASS'
for x in pr['reused_modules']:
 if x['module'] in {p['module'] for p in providers}:
  other=next(p for p in providers if p['module']==x['module']);assert other['source_sha256']==x['source_sha256'] and other['object_sha256']==x['object_sha256']
 else:providers.append(dict(x,selected_parent_record=desc(rec)))
fresh=pr['fresh_modules'][0];assert fresh['sha256']==pr['source_pass_object']['sha256']
providers.append(dict(module=fresh['module'],source=str(prog),source_sha256=sha(prog),object=fresh['path'],object_sha256=fresh['sha256'],selected_parent_record=desc(rec)))
for x in providers:
 assert sha(x['source'])==x['source_sha256']
 if x['object'] is not None:assert sha(x['object'])==x['object_sha256']
seen=set();external={'Init'}
def dfs(n):
 if not n.startswith('BusyBeaver.'):external.add(n);return
 if n in seen:return
 seen.add(n);x=next(x for x in providers if x['module']==n)
 for child in re.findall(r'^import ([A-Za-z0-9_.]+)$',pathlib.Path(x['source']).read_text(),re.M):dfs(child)
for n in units[0]['imports']:dfs(n)
assert len(seen)==22 and seen=={x['module'] for x in providers}
boundary=dict(status='SOURCE_ONLY_PROSPECTIVE_PROVIDER_PLAN',expected_project_module_count=22,current_bound_provider_count=17,
              providers=providers,external_boundaries=sorted(external),toolchain_providers=bd['toolchain_providers'],compiler=bd['compiler'],
              unselected_policy='Five new Site-chain objects are explicitly null until exact successful providers are selected. This does not assert no PASS exists elsewhere.')
assert sum(x['object'] is not None for x in providers)==17
(B/'boundary-plan.json').write_text(json.dumps(boundary,indent=2)+'\n')
manifest=dict(status='SOURCE_ONLY_PILOT_PLAN_NOT_EXECUTED',inputs=[desc(p) for p in expected],emitter=desc(pathlib.Path(__file__)),
              source_metadata_checks=dict(exact_delivered_vs_parsed203_dag_leaves=True,complete_prefix_tree=True,leaf_count=6460,full_nodes=6459,guard_count=8391,changed_paths=6241,
                                         op_counts=dict(collections.Counter(r[1] for r in sites)),maximum_depth=51,maximum_zero_run=6,maximum_one_run=12),
              unit_count=7,pilot_leaves=7,pilot_guard_cases=9,pilots=units,boundary=desc(B/'boundary-plan.json'),
              measurement_policy=dict(independent_unit_timeout_seconds=120,source_and_audit_share_budget=True,threads=1,memory_mib=4096,proof_limits='default',site_fuel=4000,header_margin=64),
              scope='No checker/Lean/symbolic execution. Selection uses source tree/data only. Actual leaf linkage is reasserted in each Lean unit; passing these seven leaves is not all8391 coverage.',
              full_schedule_frozen=False)
(B/'pilot-plan.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'plan':desc(B/'pilot-plan.json'),'boundary':desc(B/'boundary-plan.json'),'selection':[{k:x[k] for k in ['role','site_index','depth','opcode','operand','old_depth','longest_zero_run','longest_one_run','guards']} for x in units]},indent=2))
