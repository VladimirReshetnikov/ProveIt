#!/usr/bin/env python3
"""Stage exact existing bootstrap+frame evidence; never invoke proof or simulation.
Eleven actual source/audit PASSES are required. Preserve stopped generation,
correction and all captured text histories; compiled objects are described only.
No maintained write. Root reviews this builder, runs it, and installs its map.
"""
from pathlib import Path
import argparse,hashlib,json,re
B=Path('/tmp/zfc-routing245-lean')
BOOT_REVIEW=B/'bootstrap-plan/independent-complete-bootstrap-review.json'
FRAME_REVIEW=B/'bootstrap-frame/actual-frame-evidence-review.json'
PINS={str(BOOT_REVIEW):'a4cfe90e7372e69966284714bab2d804958aa12682a1c8a9dfeb421f08c5f5fd',
 str(FRAME_REVIEW):'8c009d7dec9031fbd203a6418351bc540b22bc5e280b1f5538ab7efc7f21b8bf',
 str(B/'bootstrap-chunks/group09/run1/verification.json'):'52c2be8fcfe2c959e5ef7d98d6a3bb4f27de32a92cf7b14ae65364092c92a56f',
 str(B/'bootstrap-frame/run1/verification.json'):'9b11432d5751e781a53639bd427be219055ed3615d5f88e038d36a177f3d6997'}
COMPILED=('.olean','.ilean','.olean.server','.olean.private','.o','.so','.a','.pyc','.c')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def desc(p):return dict(path=str(p),sha256=sha(p),bytes=Path(p).stat().st_size)
def load(p):return json.loads(Path(p).read_text())
def pin(p,h):need(sha(p)==h,'Changed bytes '+str(p))
def dump(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')

def actual(p,expected_module,probes,callers):
 d=load(p);need(d['status']=='PASS'and d['prepare_only']is False and d['before']==d['after'],'Incomplete actual PASS '+str(p))
 need(all(d[k]for k in ['only_standard_axioms','source_object_recorded_before_audit','all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit']),'Missing postchecks')
 need((d['named_axiom_probes'],d['callers'])==(probes,callers),'Actual census differs')
 for f,h in d['before'].items():pin(f,h)
 for key in ['source','audit']:
  q=d[key];pin(q['path'],q['sha256']);pin(q['snapshot'],q['sha256'])
 fresh=d['fresh_modules'];need(len(fresh)==1 and fresh[0]['module']==expected_module,'Wrong fresh module');f=fresh[0]
 need(all(f[k]==d['source_pass_object'][k]for k in ['module','path','sha256','source_sha256'])and f['source_sha256']==d['source']['sha256'],'Pre-audit source binding differs')
 pin(f['path'],f['sha256']);a=d['fresh_first_provider_before_audit'];need(a['module']==expected_module and a['sha256']==f['sha256'],'Wrong pre-audit provider')
 need(Path(a.get('actual_first',a.get('path'))).resolve()==Path(f['path']).resolve(),'Wrong fresh first path')
 for q in d['reused_modules']:
  pin(q['source'],q['source_sha256']);pin(q['object'],q['object_sha256']);a=next(a for a in d['actual_first_providers']if a['module']==q['module'])
  need(a['sha256']==q['object_sha256']and Path(a.get('actual_first',a.get('path'))).resolve()==Path(q['object']).resolve(),'Wrong reused first provider')
 for a in d['toolchain_providers']:pin(a['actual_first'],a['object_sha256'])
 need([c['label']for c in d['commands']]==['source','audit'],'Wrong command order')
 for c in d['commands']:
  need(c['exit_code']==0 and not c.get('timed_out',False)and c['command'][1:3]==['-j1','-M4096'],'Failed/changed command')
  need((p.parent/(c['label']+'.log')).read_text()==c['output'],'Raw command output differs')
 reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",d['commands'][1]['output'],re.S)
 parsed=[dict(name=n,axioms=[x.strip()for x in s.split(',')if x.strip()])for n,s in reports]
 names=re.findall(r'^#print axioms (\S+)$',Path(d['audit']['path']).read_text(),re.M)
 need(parsed==d['actual_axiom_sets']and [q['name']for q in parsed]==names and len(names)==probes,'Raw axiom reports differ')
 need(len(re.findall(r'^example\b',Path(d['audit']['path']).read_text(),re.M))==callers,'Typed caller count differs')
 need(all(set(q['axioms'])<={'propext','Quot.sound','Classical.choice'}for q in parsed),'Unexpected axioms')
 need(d['shared_wall_seconds']==120 and d['dependency_build']is False and d['downloads']is False and d['warnings']=={'source':0,'audit':0},'Policy/warning census differs')
 return d

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 need(__debug__,'Assertions must stay enabled');repo=a.repo.resolve();out=a.output.resolve()
 need(not out.is_relative_to(repo)and not out.is_relative_to(B)and not out.exists(),'Use a new external packet directory outside captured roots')
 for f,h in PINS.items():pin(f,h)
 br=load(BOOT_REVIEW);need(br['status']=='CLEAN_EXISTING_COMPLETE_BOOTSTRAP_EVIDENCE'and br['findings']==[]and len(br['units'])==10,'Missing complete independent bootstrap review')
 roots=[B/'bootstrap-plan',B/'bootstrap-first',B/'bootstrap-chunks',B/'bootstrap-frame']
 extras=[Path(__file__).resolve(),BOOT_REVIEW,FRAME_REVIEW]+[B/'endpoint-plan'/n for n in ['guard-template.py.in','execution-template-inventory.json','independent-frame-endpoint-source-review.json','independent-padding-and-pending-guard-review.json']]
 need(all(p.is_file()for p in extras),'Missing preservation input')
 units=[];end=0
 for i in range(10):
  U=B/'bootstrap-first'if i==0 else B/'bootstrap-chunks'/f'group{i:02}';inv=load(U/'source-inventory.json');p=U/'run1/verification.json';d=actual(p,inv['module'],len(inv['probes']),inv['callers'])
  reviewed=br['units'][i];need(reviewed['record']['path']==str(p)and reviewed['record']['sha256']==sha(p),'Actual record not independently reviewed')
  need(inv['start']==end and inv['source']['sha256']==d['source']['sha256']and inv['audit']['sha256']==d['audit']['sha256'],'Broken selected continuation')
  if i:need(inv['parents'][0]['sha256']==units[-1]['record']['sha256'],'Wrong actual predecessor')
  end=inv['endpoint'];units.append(dict(module=inv['module'],directory=str(U),record=desc(p),raw=d,endpoint=end,inventory=desc(U/'source-inventory.json'),data=desc(U/'data.json')))
 need(end==407915 and sum(u['raw']['named_axiom_probes']for u in units)==72 and sum(u['raw']['callers']for u in units)==102,'Incomplete bootstrap')
 F=B/'bootstrap-frame';p=F/'run1/verification.json';d=actual(p,'BusyBeaver.ZFC.BootstrapFrameRouting245',8,9);units.append(dict(module='BusyBeaver.ZFC.BootstrapFrameRouting245',directory=str(F),record=desc(p),raw=d,endpoint=407915))
 need((sum(u['raw']['named_axiom_probes']for u in units),sum(u['raw']['callers']for u in units))==(80,111),'Wrong family census')
 stop=B/'bootstrap-chunks/remaining03-09-run1/coordination.json';sd=load(stop)
 need(sd['status']=='STOPPED_FAILURE'and sd['active']['group']==9 and sd['active']['stage']=='GENERATION'and sd['commands'][-1]['exit_code']==1,'Original generation failure was changed')
 need('Complete proposed dispatch frame differs.'in Path(sd['commands'][-1]['output_path']).read_text(),'Missing original failure log')
 for q in sd['completed']:
  need(q['record']['sha256']==units[q['group']]['record']['sha256'],'Coordinator successful prefix differs')
 need(load(B/'bootstrap-chunks/group09/data.json')['checkpoints']['407915']['left']==[1]+[0]*9,'Wrong corrected finite target')
 # Capture all text, including unsuccessful generation and original pending variants.
 def paths():return sorted(set(p for root in roots for p in root.rglob('*')if p.is_file()or p.is_symlink())|set(extras),key=str)
 initial=paths();aliases=[];blobs={};excluded=[];captured={}
 for p in initial:
  if p.is_symlink():
   excluded.append(dict(path=str(p),kind='symlink_not_materialized',target=str(p.resolve()),sha256=sha(p)if p.is_file()else None));continue
  data=p.read_bytes();h=hashlib.sha256(data).hexdigest();captured[str(p)]=h
  if any(p.name.endswith(s)for s in COMPILED):excluded.append(dict(path=str(p),kind='compiled_or_binary_not_copied',sha256=h,bytes=len(data)));continue
  try:text=data.decode('utf-8')
  except UnicodeDecodeError:excluded.append(dict(path=str(p),kind='non_utf8_not_copied',sha256=h,bytes=len(data)));continue
  blobs.setdefault(h,dict(bytes=len(data),utf8=text));aliases.append(dict(path=str(p),sha256=h,bytes=len(data)))
 for q in aliases:need(blobs[q['sha256']]['utf8'].encode('utf-8')==Path(q['path']).read_bytes(),'History roundtrip failure')
 for u in units:
  for role in ['source','audit']:need(u['raw'][role]['sha256']in blobs,'Selected source/audit absent from history')
  need(u['record']['sha256']in blobs,'Selected raw record absent from history')
 out.mkdir();files=[];Q=repo/'Computability/BusyBeaver/Research/ZFC';L=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC';family=Q/'routing245-bootstrap';destinations=set()
 def stage_bytes(data,dest,original=None):
  need(dest not in destinations,'Duplicate mapped destination');destinations.add(dest);p=out/'files'/str(len(files))/dest.name;p.parent.mkdir(parents=True);p.write_bytes(data)
  files.append(dict(source=str(p),original=str(original)if original else None,destination=str(dest),sha256=sha(p),bytes=len(data)))
 def stage(src,dest):stage_bytes(Path(src).read_bytes(),dest,src)
 summary=[]
 for u in units:
  d=u['raw'];name=u['module'].split('.')[-1];U=Path(u['directory'])
  stage(d['source']['path'],L/(name+'.lean'));stage(d['audit']['path'],family/'audits'/(name+'Audit.lean'))
  stage(u['record']['path'],family/'records'/(name+'-verification.json'))
  stage(U/'prepared1/verification.json',family/'records'/(name+'-prepared.json'))
  for label in ['source','audit']:stage(U/'run1'/(label+'.log'),family/'logs'/(name+'-'+label+'.log'))
  stage(U/'check.py',family/'provenance'/(name+'-check.py'))
  if 'inventory'in u:
   stage(u['inventory']['path'],family/'inventories'/(name+'.json'));stage(u['data']['path'],family/'data'/(name+'.json'))
  summary.append({k:v for k,v in u.items()if k!='raw'}|dict(source=d['source'],audit=d['audit'],fresh=d['fresh_modules'][0],probes=d['named_axiom_probes'],callers=d['callers'],warnings=d['warnings'],seconds={q['label']:q['seconds']for q in d['commands']}))
 for name in ['generate.py','generate-v2.py','prepare_continuation_guard.py','prepare_continuation_guard-v2.py','continue_measured_schedule.py']:
  stage(B/'bootstrap-plan'/name,family/'provenance'/name)
 stage(Path(__file__),family/'provenance/build_packet.py')
 stage(stop,family/'coordination-stopped.json');stage(B/'bootstrap-plan/final-shape-diagnostic.json',family/'final-shape-diagnostic.json')
 stage(BOOT_REVIEW,Q/'results/routing245-bootstrap-independent-review.json');stage(FRAME_REVIEW,Q/'results/routing245-bootstrap-frame-review.json')
 stage(units[9]['record']['path'],Q/'results/routing245-bootstrap-verification.json');stage(units[10]['record']['path'],Q/'results/routing245-bootstrap-frame-verification.json')
 history=dict(schema='exact_utf8_history_v1',scope='Every captured UTF-8 file preserved byte-for-byte by hash; compiler objects and symlinks described but not copied.',roots=list(map(str,roots)),aliases=aliases,blobs=blobs,excluded=excluded)
 hp=out/'history.json';dump(hp,history);stage(hp,family/'history.json')
 scope='''Exact routing245 bootstrap and whole-tape frame evidence

The11 maintained Lean modules prove the literal blank run through407915 steps and identify its whole tape with the calibrated logical seed under DispatchFrame64. The10 bootstrap units have72 named axiom probes/102 typed callers; the frame adds8/9. All selected runs passed with zero warnings under default proof limits, -j1/-M4096 and120seconds shared by source+audit per unit.

Original generation stopped before the final source was emitted: its finite left-list expectation had one redundant exterior zero. The preserved diagnostic found state88/head−5/right707bits/351ones unchanged and left=true followed by9false. The final-only successor changes that expectation and the frame padding; earlier proofs were reused. coordination-stopped.json intentionally remains STOPPED_FAILURE. Final verification aliases are separate successful evidence.

The maintained Lean sources retain normal imports. The exact original guards/generators in provenance retain historical scratch paths and require the recorded provider caches; this packet does not promise a clean-checkout guard replay or include compiled objects. No proof, simulator, generator or version query was run by the publication builder. history.json restores each captured text alias via blobs[sha256].utf8 encoded as UTF-8 and separately lists non-copied objects/symlinks.

This package establishes bootstrap and frame facts. Complete routed-tree coverage, the closed binary consistency endpoint, and PA internalization are separately tracked. The independent bootstrap review and author-disclosed frame review retain their own scopes.
'''
 stage_bytes(scope.encode(),family/'REPLAY.md')
 publication=dict(status='PASS_BOOTSTRAP_AND_FRAME_PUBLICATION',scope='Existing exact bootstrap/frame proofs only; no coverage, binary endpoint, PA internalization or unconditional nonhalting claim.',units=summary,modules=11,bootstrap_probes=72,bootstrap_callers=102,total_probes=80,total_callers=111,total_source_seconds=sum(u['seconds']['source']for u in summary),total_audit_seconds=sum(u['seconds']['audit']for u in summary),max_source_seconds=max(u['seconds']['source']for u in summary),history=dict(destination=str(family/'history.json'),sha256=sha(hp),aliases=len(aliases),blobs=len(blobs),excluded=len(excluded)),reviews=[desc(BOOT_REVIEW),desc(FRAME_REVIEW)],failure_history=dict(path=str(stop),sha256=sha(stop),status='STOPPED_FAILURE',final_successor_record=units[9]['record']),compiled_objects_published=False,proof_replay=False,simulation_replay=False,builder=desc(Path(__file__)))
 pp=out/'publication.json';dump(pp,publication);stage(pp,Q/'results/routing245-bootstrap-publication.json')
 need(initial==paths(),'Capture file set changed during packaging')
 for p,h in captured.items():pin(p,h)
 for f,h in PINS.items():pin(f,h)
 for row in files:pin(row['source'],row['sha256'])
 dump(out/'map.json',dict(files=files,publication=desc(pp),history=desc(hp),proof_execution=False,maintained_writes=False))
 print(json.dumps(dict(map=desc(out/'map.json'),publication=desc(pp),files=len(files),history_aliases=len(aliases),history_blobs=len(blobs)),indent=2))
if __name__=='__main__':main()
