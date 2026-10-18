"""Emit three actual-tree subtree measurements; parse data only, never run proofs/checkers."""
from pathlib import Path
import collections,hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');B=Path('/tmp/zfc-routing245-lean/coverage-subtree-pilots')
L=R/'Computability/BusyBeaver/Lean';Q=R/'Computability/BusyBeaver/Research/ZFC'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=Path(p).stat().st_size)
plain=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-sites_logical.json'
prog=L/'BusyBeaver/ZFC/ProgramRouting245.lean';site=Path('/tmp/zfc-routing245-lean/site/SiteRouting245.lean')
coverage=L/'BusyBeaver/ZFC/SiteCoverage.lean'
for p,pin in [(plain,'f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745'),(prog,'060a95566e6162b845b3ee734b4134aefeeb3e9c079de705c2d094ca9119ef0b'),(site,'d05562d7a17c58a45089903977a074ea36559d39a2c5f854d63af5874c951021'),(coverage,'643aa151328a65ba292214df01a933adc46408a468faabf273bf736457393cf4')]:assert sha(p)==pin
sites=json.loads(plain.read_text());kind={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
pat=re.compile(r'^private def row(\d{3}) : Row := \((\(\.[a-z]+ \d+\)|\.halt), (\(\.[a-z]+ \d+\)|\.halt)\)$',re.M)
def ep(s):v=s.strip('()').removeprefix('.').split();return(v[0],int(v[1])if len(v)>1 else None)
rows={int(m[1]):(ep(m[2]),ep(m[3]))for m in pat.finditer(prog.read_text())};assert set(rows)==set(range(203))
expanded=[]
def expand(i,p):
 for b,e in zip('01',rows[i]):
  if e[0]=='node':assert e[1]<i;expand(e[1],p+b)
  else:expanded.append((p+b,e))
expand(202,'');assert expanded==[(p,(kind[k],a))for p,k,a in sites]
leaf={p:(i,k,a)for i,(p,k,a)in enumerate(sites)};meta={}
def build(p):
 if p in leaf:
  i,k,a=leaf[p];m=dict(lo=i,hi=i+1,leaves=1,guards=2 if k=='CD'else 1,height=0,nodes=0)
 else:
  a,b=build(p+'0'),build(p+'1');assert a['hi']==b['lo']
  m=dict(lo=a['lo'],hi=b['hi'],leaves=a['leaves']+b['leaves'],guards=a['guards']+b['guards'],height=1+max(a['height'],b['height']),nodes=1+a['nodes']+b['nodes'])
 meta[p]=m;return m
assert build('')==dict(lo=0,hi=6460,leaves=6460,guards=8391,height=51,nodes=6459)
frontier=[]
def split(p):
 if meta[p]['guards']<=64:frontier.append(dict(path=p,**meta[p]));return
 split(p+'0');split(p+'1')
split('');assert len(frontier)==236 and sum(x['guards']for x in frontier)==8391 and sum(x['leaves']for x in frontier)==6460
assert all(a['hi']==b['lo']for a,b in zip(frontier,frontier[1:]))
# Only three complementing cuts are emitted, not a production coverage schedule.
selected=[(70,'deepest_routes'),(174,'max_guard_long_one_run'),(0,'short_prefix_baseline')]
assert all(frontier[70]['lo']<=i<frontier[70]['hi']for i in [1703,1704,1705])
assert frontier[174]['guards']==max(x['guards']for x in frontier)==61
bits=lambda p:'['+', '.join('true'if b=='1'else'false'for b in p)+']'
units=[]
for index,role in selected:
 cut=frontier[index];p=cut['path'];m=f'SitesRouting245CutPilot{index:03d}';ns='SetTheory.BusyBeaver.ZFC.'+m
 goal=f'allSites SiteRouting245.checkSite {bits(p[::-1])}\n      (descend TreeRouting245.tree {bits(p)}) = true'
 source=f'''import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245

/-!
Exact routed subtree measurement {index}: {cut['leaves']} leaves / {cut['guards']} guards.
Both decrement guards are included by SiteRouting245.checkSite. This closed
check is about the actual imported subtree with its complete reverse prefix.
Fuel 4000 and margin 64 are unchanged. No complete coverage or endpoint is
asserted. The cut is only a measurement candidate until root checks it.
-/
namespace {ns}
open RegisterPath RMBisim SiteCoverage

 theorem checked :
    {goal} := by
  decide +kernel

end {ns}
'''.replace('\n theorem checked','\ntheorem checked')
 audit=f'''import BusyBeaver.ZFC.{m}

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage {m}

#print axioms {ns}.checked

example : {goal} := checked

example (Q : List Bool) (e : Edge)
    (hl : LeafAt (descend TreeRouting245.tree {bits(p)}) Q e) :
    SiteRouting245.checkSite ({bits(p[::-1])}.reverse ++ Q) e = true :=
  allSites_sound SiteRouting245.checkSite hl {bits(p[::-1])} checked
'''
 out=B/f'cut{index:03d}';out.mkdir();sp=out/(m+'.lean');ap=out/'Audit.lean';sp.write_text(source);ap.write_text(audit)
 members=sites[cut['lo']:cut['hi']]
 assert all(q.startswith(p)for q,k,a in members)
 assert [(q,k,a)for q,k,a in sites if q.startswith(p)]==[tuple(r)for r in members]
 entry=dict(index=index,role=role,module='BusyBeaver.ZFC.'+m,**cut,prefix_length=len(p),maximum_absolute_depth=len(p)+cut['height'],
            op_counts=dict(collections.Counter(k for q,k,a in members)),members=[dict(index=i,path=q,opcode=k,operand=a,guards=2 if k=='CD'else 1)for i,(q,k,a)in enumerate(members,start=cut['lo'])],
            source=desc(sp),audit=desc(ap),probes=1,callers=2,imports=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SiteRouting245'],status='SOURCE_ONLY_NOT_COMPILED')
 units.append(entry)
# Select the exact22 underlying providers already observed by root's first leaf
# check, not the fresh leaf object itself, plus the unchanged generic coverage.
pr=Path('/tmp/zfc-routing245-lean/coverage-pilots/leaf1704-run1/case1704/verification.json')
assert sha(pr)=='659ccf67b43f136e932125ad6f7ed5d1b3575d0769b94e0c95d64347ed0d8bc4'
d=json.loads(pr.read_text());assert d['status']=='PASS' and d['project_module_count']==22
providers=[]
for x in d['reused_modules']:
 actual=next(y for y in d['actual_first_providers']if y['module']==x['module'])
 assert Path(actual['actual_first']).resolve()==Path(x['object']).resolve() and actual['sha256']==x['object_sha256']
 assert all(d['before'][x[k]]==d['after'][x[k]]==x[k+'_sha256']==sha(x[k])for k in ['source','object'])
 providers.append(dict(x,selected_parent_record=desc(pr)))
old=Q/'results/prefix246-runtime-verification.json';od=json.loads(old.read_text());assert od['status']=='PASS'
x=next(y for y in od['reused_modules']if y['module']=='BusyBeaver.ZFC.SiteCoverage')
assert all(od['before'][x[k]]==od['after'][x[k]]==x[k+'_sha256']==sha(x[k])for k in ['source','object'])
a=next(y for y in od['actual_first_providers']if y['module']==x['module'])
assert Path(a['actual_first']).resolve()==Path(x['object']).resolve() and a['sha256']==x['object_sha256']
providers.append(dict(x,selected_parent_record=desc(old)))
closure=[];tool={'Init'}
def dfs(n):
 if not n.startswith('BusyBeaver.'):tool.add(n);return
 if n in closure:return
 x=next(x for x in providers if x['module']==n)
 for child in re.findall(r'^import ([A-Za-z0-9_.]+)$',Path(x['source']).read_text(),re.M):dfs(child)
 closure.append(n)
for n in units[0]['imports']:dfs(n)
assert len(closure)==23 and set(closure)=={x['module']for x in providers} and tool=={'Init','Lean.Elab.Tactic.Omega'}
boundary=dict(status='SOURCE_ONLY_SELECTED_EXISTING_PROVIDER_INVENTORY',providers=[next(x for x in providers if x['module']==n)for n in closure],project_count=23,external_boundaries=sorted(tool),compiler=d['compiler'],toolchain_providers=d['toolchain_providers'],proof_execution=False,guard_execution=False)
(B/'boundary-plan.json').write_text(json.dumps(boundary,indent=2)+'\n')
manifest=dict(status='SOURCE_ONLY_SUBTREE_MEASUREMENT_PLAN',emitter=desc(Path(__file__)),inputs=[desc(p)for p in [plain,prog,site,coverage]],
              exact_complete_tree_leaf_count=6460,exact_complete_tree_guard_count=8391,maximum_tree_depth=51,
              metadata_frontier=dict(cap_guards=64,cut_count=236,largest_cut_guards=61,production_schedule_frozen=False),
              selected_units=units,total_selected_leaves=sum(u['leaves']for u in units),total_selected_guards=sum(u['guards']for u in units),
              preferred_order=[70,174,0],additional_candidate_not_emitted=dict(index=67,role='zero_run_neighborhood',**frontier[67]),
              probes=3,callers=6,boundary=desc(B/'boundary-plan.json'),site_fuel=4000,header_margin=64,
              proof_policy=dict(each_source_audit_shared_seconds=120,threads=1,memory_mib=4096,proof_limits='defaults'),
              no_supplied_checker=True,no_symbolic_execution=True,no_compiler=True,no_full_schedule=True)
(B/'subtree-plan.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('plan',sha(B/'subtree-plan.json'),'boundary',sha(B/'boundary-plan.json'))
for u in units:print(u['index'],u['role'],u['lo'],u['hi'],u['leaves'],u['guards'],u['maximum_absolute_depth'],u['source']['sha256'],u['audit']['sha256'])
