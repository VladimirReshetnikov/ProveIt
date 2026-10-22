"""Independent metadata audit; reads sources/records, executes no build helper."""
from pathlib import Path
import re,json,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');D=Path(__file__).resolve().parent;P=Path('/tmp/k215-phase17-check/plan.json');B=Path('/tmp/k215-phase17-check/build.py')
ROOTS=['Computability/BusyBeaver/Lean','Logic/FirstOrder/Lean','SetTheory/ZF/Lean','SetTheory/BoundedConsistency/Lean'];STD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
pattern=r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)"
def profiles(t):return [[n,sorted(set(a.strip()for a in ax.split(',')if a.strip()))]for n,ax in re.findall(pattern,t)]
def clean(t):
 out=[];i=0;depth=0
 while i<len(t):
  if t[i:i+2]=='/-':depth+=1;i+=2
  elif depth and t[i:i+2]=='-/':depth-=1;i+=2
  elif depth:out.append('\n'if t[i]=='\n'else' ');i+=1
  elif t[i:i+2]=='--':j=t.find('\n',i);i=len(t)if j<0 else j
  elif t[i]=='"':
   i+=1
   while i<len(t):
    if t[i]=='\\':i+=2
    elif t[i]=='"':i+=1;break
    else:i+=1
  else:out.append(t[i]);i+=1
 assert depth==0
 return ''.join(out)
def imports(p):return [n for l in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)',clean(Path(p).read_text()))for n in l.split()]
plan=read(P);planpin=sha(P);helperpin=sha(B)
historical={};histrows={};rawcoverage={};commands_later_changed=[]
for dirname,expected,count in [('/tmp/k215-phase16-check/primary-run1','3ded969c86762960cda923b7d9aee63953125185a2bb3f64c535d5fe4104462f',195),('/tmp/k215-phase16-check/compatibility-run1','f16fa4191d1d27864449582d0c40f3ba28eed34a821d53776b75ef2eb6582ddb',78)]:
 p=Path(dirname);assert sha(p/'result.json')==expected
 result=read(p/'result.json');assert result['status']=='PASS';inv=read(p/'inventory.json');done=read(p/'completed.json');assert sha(p/'inventory.json')==result['inventory_sha256']and sha(p/'completed.json')==result['completed_sha256'];assert len(done)==len(inv['modules'])==count
 entries={x['module']:x for x in inv['modules']};assert len(entries)==count
 for m,rec in done.items():
  row=entries[m];source=p/'workspace'/(m.replace('.','/')+'.lean');obj=p/'objects'/(m.replace('.','/')+'.olean')
  assert sha(source)==row['source_sha256']==rec['source_sha256'];assert sha(obj)==rec['object_sha256'];assert sha(rec['log'])==rec['log_sha256'];assert imports(source)==row['imports'];assert rec['dependencies']=={d:done[d]['object_sha256']for d in row['imports']if d!='Init'}
  assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
  if 'command'in rec:
   cmd=rec['command'];assert cmd[:3]==['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M12288']and cmd[-1]==rec['source']
   if Path(rec['source']).exists()and sha(rec['source'])!=rec['source_sha256']:commands_later_changed.append({'module':m,'old_command_source':rec['source'],'accepted_snapshot':str(source),'old_sha256':rec['source_sha256'],'current_command_source_sha256':sha(rec['source'])})
  rawpath=Path(rec['log']).with_name('record.json');raw=None
  if rawpath.is_file():
   raw=read(rawpath)
   for k in ['module','status','source_sha256','dependencies','log_sha256']:assert raw[k]==rec[k],(m,k)
   if 'object_sha256'in raw:assert raw['object_sha256']==rec['object_sha256']
   for k in ['command','exit_code','timed_out']:
    if k in rec:assert raw[k]==rec[k],(m,k)
   assert raw['exit_code']==0 and not raw['timed_out'];assert raw['command'][:3]==['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M12288']
  rawcoverage[m]={'raw_path':str(rawpath)if raw is not None else None,'raw_has_object_hash':bool(raw is not None and'object_sha256'in raw)}
  if m in historical:assert historical[m]['object_sha256']==rec['object_sha256']and histrows[m]['source_sha256']==row['source_sha256']and histrows[m]['imports']==row['imports']
  historical[m]=rec;histrows[m]=row
assert len(historical)==212
rows=plan['modules'];selected={x['module']:x for x in rows};assert len(selected)==len(rows)==213
canonical=[];oldclients=[];newbounds=[]
for row in rows:
 m=row['module'];assert sha(row['source'])==row['source_sha256'];assert imports(row['source'])==row['imports']
 found=[R/r/(m.replace('.','/')+'.lean')for r in ROOTS if (R/r/(m.replace('.','/')+'.lean')).is_file()]
 if found:
  assert len(found)==1;assert sha(found[0])==row['source_sha256'];canonical.append({'module':m,'path':str(found[0]),'sha256':row['source_sha256']})
 elif m in historical:
  assert row['source_sha256']==histrows[m]['source_sha256'];oldclients.append(m)
 else:assert m=='DirectSeed17Api'
 if m in historical:assert row['expected_reports']==profiles(Path(historical[m]['log']).read_text()),m
 elif 'expected_reports'in row:assert row['expected_reports']==[],m
 else:
  assert row['allowed_report_axioms']==sorted(STD);newbounds.append({'module':m,'names':row['expected_report_names']})
 if not found:assert row.get('warnings_forbidden')is True
visited=set();active=set();order=[]
def visit(m):
 if m=='Init':return
 assert m in selected and m not in plan['retired_modules']
 if m in visited:return
 assert m not in active;active.add(m)
 for d in selected[m]['imports']:visit(d)
 active.remove(m);visited.add(m);order.append(m)
for m in plan['targets']:visit(m)
assert order==[r['module']for r in rows]
changed={m for m,r in selected.items()if m not in historical or(r['source_sha256'],r['imports'])!=(histrows[m]['source_sha256'],histrows[m]['imports'])}
forced=set(changed)
while True:
 more=forced|{m for m,r in selected.items()if set(r['imports'])&forced}
 if more==forced:break
 forced=more
assert plan['expected']['changed_sources']==sorted(changed)and plan['expected']['fresh_by_source_transitivity']==sorted(forced)
sites=[m for m in selected if 'KSites215Batch'in m];assert len(sites)==9 and set(sites)<=forced
for p,pin in plan['present_inputs'].items():assert sha(p)==pin,p
for p in plan['absent_inputs']:assert not Path(p).exists()and not Path(p).is_symlink(),p
assert set(plan['retired_modules']).isdisjoint(selected)
oldaudits={r['module']:r for r in read(Path('/tmp/k215-phase16-check/primary-run1/result.json'))['audits']}
for audit in plan['audits']:
 assert sha(audit['source'])==audit['source_sha256'];assert audit['warnings_forbidden']is True
 expected=[[n,sorted(set(a.strip()for a in ax.split(',')if a.strip()))]for n,ax in oldaudits[audit['module']]['named_reports']]
 assert audit['expected_reports']==expected
# Same toolchain identity is retained and every manifest pin matches current bytes.
tool=read('/tmp/k215-phase16-check/primary-run1/toolchain.json');assert tool==read('/tmp/k215-phase16-check/compatibility-run1/toolchain.json')
for key in ['lean','lake','Init.olean','project_toolchain']:assert sha(tool[key]['path'])==tool[key]['sha256']
assert sha(P)==planpin and sha(B)==helperpin
out={'status':'PASS_FROZEN_METADATA_INVARIANTS','plan_sha256':planpin,'runner_sha256':helperpin,'provider_count':len(rows),'canonical_project_count':len(canonical),'old_exact_client_count':len(oldclients),'new_typed_client_count':1,'changed_count':len(changed),'forced_fresh_count':len(forced),'reusable_count':len(rows)-len(forced),'site_batches_forced_fresh':sites,'new_profile_discovery_bounds':newbounds,'canonical_bindings':canonical,'historical_basis_count':len(historical),'historical_raw_records_present':sum(r['raw_path']is not None for r in rawcoverage.values()),'historical_adjacent_raw_records_absent':sum(r['raw_path']is None for r in rawcoverage.values()),'historical_raw_missing_object_hash':[m for m,r in rawcoverage.items()if r['raw_path']is not None and not r['raw_has_object_hash']],'accepted_old_command_source_later_changed':commands_later_changed,'present_inputs_count':len(plan['present_inputs']),'absent_inputs_count':len(plan['absent_inputs']),'endpoint_audit_count':len(plan['audits']),'compiler_or_runner_invoked':False}
(D/'metadata-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in['canonical_bindings','accepted_old_command_source_later_changed']},indent=2));print('later_changed_old_command_sources',len(commands_later_changed))
