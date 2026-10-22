#!/usr/bin/env python3
"""Own read-only documentation/record checks. No compiler, generator or imports from delivery."""
import collections,hashlib,json,pathlib,re,subprocess,urllib.parse
R=pathlib.Path('/home/codex/.codex/worktrees/ec20/Proofs')
O=pathlib.Path('/tmp/k215-phase12-documentation-peer')
P=pathlib.Path('/tmp/k215-phase12-import-proposal')
BASE=pathlib.Path('/tmp/k215-generic-cd58-check/inline-full-run1')
PRI=pathlib.Path('/tmp/k215-phase12-import-check/primary-run1')
COM=pathlib.Path('/tmp/k215-phase12-import-check/compatibility-run1')
PH=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase12'
pins={}
def raw(p):
 p=pathlib.Path(p);b=p.read_bytes();pins[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)};return b
def js(p):return json.loads(raw(p))
def sha(p):return hashlib.sha256(raw(p)).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
def closure(inv,root):
 rows={r['module']:r for r in inv['modules']};out=set()
 def go(m):
  if m not in rows:return
  if m in out:return
  out.add(m)
  for d in rows[m]['imports']:go(d)
 go(root);return out
report={'status':'PASS_BOUNDED_DOCUMENTATION_PEER','findings':[],
 'scope':'Full seven documentation deltas and incoming checkpoint paragraph read; independent bounded source/record/metric/link checks, not compiler execution, object validation or new mathematical proof audit.'}
expected_docs=js(P/'documentation-map.json')['files']
paths=list(dict.fromkeys([R/r['path'] for r in expected_docs]+[R/'docs/incoming/README.md']))
docs=[];links=[];map_deltas=[]
for p in paths:
 b=raw(p);rel=str(p.relative_to(R));docs.append({'path':rel,**pins[str(p)]})
 recorded=next((x for x in expected_docs if x['path']==rel),None)
 if recorded and (recorded['sha256']!=hashlib.sha256(b).hexdigest() or recorded['bytes']!=len(b)):
  assert p==PH/'README.md';map_deltas.append({'path':rel,'recorded':recorded,'current':pins[str(p)],'reason':'Root disclosed overview wording update; current reviewed bytes bound here.'})
 if p==PH/'README.md':added=b.decode()
 else:
  delta=git('diff','--unified=0','--',rel).decode();added='\n'.join(l[1:] for l in delta.splitlines() if l.startswith('+') and not l.startswith('+++'))
 for target in re.findall(r'(?<!!)\[[^\]]*\]\(([^)]+)\)',added):
  target=target.strip('<>');u=urllib.parse.urlsplit(target)
  if u.scheme or u.netloc:continue
  dest=(p.parent/urllib.parse.unquote(u.path)).resolve() if u.path else p
  exists=dest.exists();pending=dest==PH/'lean/README.md'
  assert exists or pending,(p,target)
  if exists and u.fragment and dest.suffix=='.md':
   heads=[]
   for line in dest.read_text().splitlines():
    if re.match(r'^#{1,6} ',line):
     s=re.sub(r'^#{1,6} +','',line).strip().lower();s=re.sub(r'[^\w\- ]','',s);heads.append(s.replace(' ','-'))
   assert urllib.parse.unquote(u.fragment) in heads,(target,heads)
  links.append({'from':rel,'target':target,'resolved':str(dest.relative_to(R)),'exists':exists,'pending_packet':pending and not exists})
old_incoming=git('show','HEAD:docs/incoming/README.md').decode()
new_incoming=(R/'docs/incoming/README.md').read_text()
assert old_incoming.split('## Current queue',1)[1]==new_incoming.split('## Current queue',1)[1]
report.update(documents=docs,map_deltas=map_deltas,scoped_links=links,incoming_queue_and_history_exact=True)
pinv=js(PRI/'inventory.json');cinv=js(COM/'inventory.json');binv=js(BASE/'inventory.json')
pdone=js(PRI/'completed.json');cdone=js(COM/'completed.json');bdone=js(BASE/'completed.json')
pr=js(PRI/'result.json');cr=js(COM/'result.json')
assert pr['status']==cr['status']=='PASS'
for root,res in [(PRI,pr),(COM,cr)]:
 assert sha(root/'inventory.json')==res['inventory_sha256'];assert sha(root/'completed.json')==res['completed_sha256']
pclosure=closure(pinv,'BusyBeaver.ZFC.KEndpoint215');bclosure=closure(binv,'BusyBeaver.ZFC.KEndpoint215')
assert len(pclosure)==179 and len(bclosure)==192 and len(pdone)==184
compat_projects=set(cdone)-{'WFModelCompat12','ZFNativeCompat12'}
assert len(compat_projects)==67 and len(set(pdone)|compat_projects)==199
assert len(set(pdone)&compat_projects)==52
orig=lambda rows:dict(collections.Counter(r['origin'] for r in rows.values()))
assert orig(pdone)=={'phase11_checked':169,'candidate_fresh':15}
assert orig(cdone)=={'secondary_checked':52,'phase11_checked':12,'candidate_fresh':5}
assert len(bclosure-pclosure)==15 and len(pclosure-bclosure)==2
# Check current/old source byte measurements and the seven-file net change.
adopt=js(P/'adoption.json');bef={pathlib.Path(x['target']).stem:x for x in adopt['files'] if x['target'].endswith('.lean')}
assert len(bef)==7
for x in adopt['files']:
 assert sha(R/x['target'])==x['sha256']
 if x['archived_before']:assert sha(x['archived_before'])==x['before_sha256']
def size(rows,selected,old=False):
 total=0
 for r in rows['modules']:
  if r['module'] not in selected:continue
  p=pathlib.Path(r['source']);b=raw(p)
  if hashlib.sha256(b).hexdigest()!=r['source_sha256']:
   assert old
   p=pathlib.Path(bef[r['module'].split('.')[-1]]['archived_before']);b=raw(p)
  assert hashlib.sha256(b).hexdigest()==r['source_sha256'],r['module'];total+=len(b)
 return total
oldbytes=size(binv,bclosure,True);newbytes=size(pinv,pclosure)
assert (oldbytes,newbytes,oldbytes-newbytes)==(2362942,2129439,233503)
net=sum(x['bytes']-(len(raw(x['archived_before'])) if x['archived_before'] else 0) for x in bef.values())
assert net==491
# All selected logs are read and pinned; do not claim object rechecking.
def logs(rows):
 out={}
 for m,r in rows.items():
  b=raw(r['log']);assert hashlib.sha256(b).hexdigest()==r['log_sha256'],m
  s=b.decode();assert r['status']=='PASS'
  out[m]={'origin':r['origin'],'warning_occurrences':len(re.findall(r': warning:',s)),'log_sha256':r['log_sha256']}
 return out
plogs=logs(pdone);clogs=logs(cdone)
fw=sum(x['warning_occurrences'] for x in plogs.values() if x['origin']=='candidate_fresh')
rw=sum(x['warning_occurrences'] for x in plogs.values() if x['origin']!='candidate_fresh')
assert (fw,rw)==(4,16)
assert sum(x['warning_occurrences'] for x in clogs.values() if x['origin']=='candidate_fresh')==0
preexisting=[]
for m,r in pdone.items():
 if r['origin']=='candidate_fresh' and plogs[m]['warning_occurrences']:
  before=raw(bdone[m]['log']).decode();assert hashlib.sha256(before.encode()).hexdigest()==bdone[m]['log_sha256']
  after=raw(r['log']).decode()
  normalize=lambda s:re.sub(r'(?m)^.*?\.lean:(\d+:\d+: warning:)','SOURCE:\\1',s)
  assert normalize(before)==normalize(after),m
  preexisting.append(m)
standard={'propext','Classical.choice','Quot.sound'}
def reports(s):
 return [(m.group(1),tuple(a.strip() for a in m.group(2).split(',') if a.strip())) for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",s,re.S)]
expected_audits={
 'EndpointAudit215':[('EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation',standard),('EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent',standard)],
 'K215Audit':[(n,a) for n,a in [
 ('SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation',standard),('SetTheory.BusyBeaver.ZFC.KEndpoint215.nonhalting_iff_zfc_consistency',standard),('SetTheory.BusyBeaver.ZFC.KDense215.commutes',{'propext'}),('SetTheory.BusyBeaver.ZFC.KBoot215.boot',{'propext','Quot.sound'}),('SetTheory.BusyBeaver.ZFC.KSites215.covered',{'propext','Quot.sound'}),('SetTheory.BusyBeaver.ZFC.KEndpoint215.p215_boot_iff',standard),('K215Audit.blank_halts_exact',standard),('K215Audit.nonhalting_exact',standard)]]}
endpoint=[]
for a in pr['audits']:
 s=raw(a['log']).decode();assert sha(a['log'])==a['log_sha256'];assert sha(a['source'])==a['source_sha256']
 assert a['exit_code']==0 and not a['timed_out'] and ': warning:' not in s
 rr=reports(s);assert [(n,set(ax)) for n,ax in rr]==expected_audits[a['module']],rr
 endpoint.extend(rr)
assert len(endpoint)==10
comp_reports={}
for m,n in [('WFModelCompat12',3),('ZFNativeCompat12',7),('BusyBeaver.ZFC.WFTheory',5)]:
 rr=reports(raw(cdone[m]['log']).decode());assert len(rr)==n
 assert all(set(a)<=standard for _,a in rr);comp_reports[m]=rr
# Preserved exact computational source/site bindings are measured against phase eleven.
site_modules=sorted(m for m in pdone if re.fullmatch(r'BusyBeaver.ZFC.KSites215Batch\d+',m))
assert len(site_modules)==9
for m in site_modules:
 assert pdone[m]['origin']=='phase11_checked'
 for k in ['source_sha256','object_sha256','log_sha256']:assert pdone[m][k]==bdone[m][k]
for m in ['BusyBeaver.ZFC.DominatedImplication','BusyBeaver.ZFC.DomRho8','BusyBeaver.ZFC.KEndpoint215']:
 assert pdone[m]['source_sha256']==bdone[m]['source_sha256']
report['actual_checks']={'primary':{'endpoint':179,'union':184,'origins':orig(pdone),'warning_counts':{'fresh_preexisting':fw,'inherited':rw},'preexisting_warning_modules':preexisting,'endpoint_reports':endpoint},'compatibility':{'project_modules':67,'clients':2,'origins':orig(cdone),'reports':comp_reports,'fresh_warnings':0},'distinct_project_modules':199,'source_metrics':{'old_selected_bytes':oldbytes,'new_selected_bytes':newbytes,'selected_reduction':oldbytes-newbytes,'seven_source_file_growth':net},'retained_site_batches':site_modules}
for p in [P/'root-actual-review.json',P/'current-review.json',P/'producer-review.json',P/'producer-literal-check.json',PH/'integration/source-metrics.json',PH/'source-peer/review.json']:raw(p)
report['bound_inputs']=pins
report['reader_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
report['exclusions']=['No compiler or supplied producer executed.','No new proof/body/axiom correctness review beyond documentation and named saved reports.','No revalidation of all compiled object bytes; root actual/current reviews are explicitly cited for that boundary.','The phase12 Lean README link is checked for existence only; this review does not validate the newly published packet or saved reader.']
(O/'review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'review_sha256':sha(O/'review.json'),'documents':len(docs),'scoped_links':len(links),'pending_links':sum(r['pending_packet'] for r in links),'map_deltas':map_deltas},indent=2))
