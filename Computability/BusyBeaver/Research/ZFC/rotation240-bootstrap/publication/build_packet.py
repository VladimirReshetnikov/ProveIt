#!/usr/bin/env python3
"""Root-only metadata publication of the completed Rotation240 bootstrap chain."""
from pathlib import Path
import argparse,gzip,hashlib,json,re
B=Path('/tmp/zfc-rotation240-bootstrap-publication-design')
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
Z=Path('Computability/BusyBeaver/Research/ZFC');L=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
F=Z/'rotation240-bootstrap'
INPUT_SHA='01325dbb00b33f830270bbfa193f96045b05233f8fcdcd7197dc4ee799a4eace'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
enc=lambda x:(json.dumps(x,indent=2)+'\n').encode()
def need(v,m):
 if not v:raise RuntimeError(m)
def load(p):return json.loads(Path(p).read_text())
def desc(p):return dict(path=str(Path(p)),sha256=sha(p))
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output.resolve()
need(isinstance(INPUT_SHA,str),'Unfrozen publication input pin')
need(not out.exists() and not out.is_relative_to(ROOT) and not out.is_relative_to(Path('/home/codex/src/Proofs')) and not out.is_relative_to(B),'Fresh external output required')
need(sha(B/'inputs.json')==INPUT_SHA,'Frozen publication inventory');plan=load(B/'inputs.json');tracked={}
def pin(path,h):
 path=str(Path(path).absolute());need(path not in tracked or tracked[path]==h,'Conflicting input pin')
 if path not in tracked:need(sha(path)==h,'Changed input '+path);tracked[path]=h
pin(B/'inputs.json',INPUT_SHA);pin(__file__,sha(__file__))
need(all(not out.is_relative_to(Path(q)) for q in plan['history_roots']),'Output overlaps selected history')
for d in plan['history']:
 pin(d['path'],d['sha256']);need(not Path(d['path']).is_symlink(),'No history symlinks');Path(d['path']).read_bytes().decode('utf-8')
pin(plan['review']['path'],plan['review']['sha256']);review=load(plan['review']['path'])
need(review['status']=='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS' and review['findings']==[],'Existing actual review')
need((review['steps'],review['blocks'],review['probes'],review['callers'],review['warnings'])==(409691,34,72,102,0),'Complete reviewed census')
pin(review['reviewer_source']['path'],review['reviewer_source']['sha256'])
need(plan['units']==review['units'] and len(plan['units'])==10,'Exact selected reviewed units')
pin(plan['batch']['path'],plan['batch']['sha256']);batch=load(plan['batch']['path'])
need(batch['status']=='PASS_EXACT_409691_PREFIX' and batch['target']==409691 and len(batch['units'])==8,'Actual terminal serial driver')
need(len(batch['commands'])==32 and all(c['exit_code']==0 for c in batch['commands']),'Actual serial phase completion')
for c in batch['commands']:pin(c['log'],c['log_sha256'])
entries={};units=[];endpoint=0;segments=0;probes=0;callers=0;prior=None
def put(target,data,origin):
 need(not target.is_absolute() and '..' not in target.parts and str(target) not in entries,'Unsafe or duplicate target')
 entries[str(target)]=(data,origin)
def copy(source,target):put(target,Path(source).read_bytes(),str(source))
for u in plan['units']:
 slug=u['unit'];v=u['verification'];pin(v['path'],v['sha256']);r=load(v['path']);base=Path(v['path']).parent.parent
 need(r['status']=='PASS' and r['prepare_only'] is False and (r['named_axiom_probes'],r['callers'],r['warnings'])==(u['probes'],u['callers'],0),'Actual clean proof pair')
 need(r['before']==r['after'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit'] and r['only_standard_axioms'],'Actual postchecks')
 need((r['shared_timeout_seconds'],r['memory_mebibytes'],r['LEAN_NUM_THREADS'])==(120,4096,'1') and r['global_option_overrides']==[],'Unchanged default policy')
 need(not any(r[k] for k in ['compiler_version_query_performed','dependency_build','downloads']),'Unexpected execution mode')
 for path,h in r['before'].items():pin(path,h)
 need(len(r['reused_modules'])==r['exact_project_prerequisite_count']==u['providers']==u['index']+4,'Exact growing provider census')
 need(set(x['module'] for x in r['toolchain_providers'])=={'Init','Lean.Elab.Tactic.Omega'},'Tool boundary')
 for role in ('source','audit'):
  need({k:r[role][k] for k in ('path','sha256')}==u[role],'Reviewed proof bytes');pin(r[role]['path'],r[role]['sha256']);pin(r[role]['snapshot'],r[role]['sha256'])
 pin(u['guard']['path'],u['guard']['sha256']);need(r['before'][u['guard']['path']]==u['guard']['sha256'],'Executed guard identity')
 need(r['boundary']==u['boundary'],'Exact recorded boundary');pin(u['boundary']['path'],u['boundary']['sha256'])
 need([c['label'] for c in r['commands']]==['source','audit'],'Sequential source/audit')
 for c in r['commands']:
  need(c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None,'Actual command completed')
  need(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'],'Compiler defaults')
  pin(c['log'],c['log_sha256']);need(Path(c['log']).read_text()==c['output'],'Exact raw log')
  need('warning:' not in c['output'] and 'sorryAx' not in c['output'],'Clean raw output')
  copy(c['log'],F/slug/(c['label']+'.log'))
 need(sum(c['seconds'] for c in r['commands'])<120,'Shared source/audit deadline')
 audit=Path(r['audit']['path']).read_text();names=re.findall(r'^#print axioms (\S+)\s*$',audit,re.M)
 raw=[dict(name=n,axioms=sorted({x.strip() for x in ax.split(',') if x.strip()})) for n,ax in re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",r['commands'][1]['output'],re.M)]
 need(raw==r['axiom_reports'] and names==[x['name'] for x in raw] and len(names)==u['probes'],'Exact ordered raw reports')
 need(len(re.findall(r'^example\b',audit,re.M))==u['callers'] and all(set(x['axioms'])<={'propext','Quot.sound'} for x in raw),'Typed callers and actual axiom set')
 need(len(r['fresh_modules'])==1 and r['source_object_recorded_before_audit'],'Fresh object recorded')
 fresh=r['fresh_modules'][0];pin(fresh['path'],fresh['sha256'])
 need(fresh==u['fresh_module'] and fresh['module']==u['module'] and fresh['source_sha256']==u['source']['sha256'],'Reviewed fresh source binding')
 need(r['source_pass_object']==dict(fresh,source_command_index=0) and r['fresh_first_provider_before_audit']=={k:fresh[k] for k in ('module','path','sha256')},'Pre-audit capture')
 pin(u['preparation']['path'],u['preparation']['sha256']);pr=load(u['preparation']['path'])
 need(pr['status']=='PREPARED_NOT_BUILT' and pr['prepare_only'] and pr['commands']==pr['fresh_modules']==[] and pr['before']==pr['after'] and pr['all_input_provider_postchecks'],'Separate unbuilt preparation')
 for path,h in pr['before'].items():pin(path,h)
 need(pr['reused_modules']==r['reused_modules'] and pr['toolchain_providers']==r['toolchain_providers'],'Prepared same objects')
 pin(u['inventory']['path'],u['inventory']['sha256']);inv=load(u['inventory']['path']);pin(u['data']['path'],u['data']['sha256'])
 need(inv['module']==u['module'] and inv['segments']==u['segments'] and inv['start']==u['start']==endpoint,'Contiguous selected inventory')
 if prior:need(inv['parents']==[dict(prior['verification'],module=prior['module'])],'Exact prior successful record')
 for s in u['segments']:
  need(s['start']==endpoint and s['end']==endpoint+2**s['depth'] and 0<=s['depth']<=14,'Exact block arithmetic');endpoint=s['end'];segments+=1
 need(endpoint==u['endpoint']==inv['endpoint'],'Exact checkpoint endpoint');prior=u
 module=u['module'].rsplit('.',1)[1];copy(u['source']['path'],L/(module+'.lean'));copy(u['audit']['path'],F/slug/'Audit.lean')
 for role,name in [('guard','check.py'),('boundary','boundary.json'),('inventory','source-inventory.json'),('data','data.json'),('preparation','preparation.json')]:copy(u[role]['path'],F/slug/name)
 dest=Z/'results'/('rotation240-bootstrap-verification.json' if u['index']==9 else 'rotation240-bootstrap-'+slug+'-verification.json');copy(v['path'],dest)
 units.append(dict(u,maintained_source=str(L/(module+'.lean')),maintained_audit=str(F/slug/'Audit.lean'),maintained_result=str(dest)))
 probes+=u['probes'];callers+=u['callers']
need((endpoint,segments,probes,callers)==(409691,34,72,102),'Complete publication census')
history=[dict(d,text=Path(d['path']).read_bytes().decode('utf-8')) for d in plan['history']]
history.extend([dict(desc(__file__),text=Path(__file__).read_text()),dict(desc(B/'inputs.json'),text=(B/'inputs.json').read_text())])
raw=enc(dict(scope='Exact frozen bootstrap source, proposals, guards, preparations, actual logs and records, driver and reviews; compiled caches excluded.',files=history))
packed=gzip.compress(raw,mtime=0);need(gzip.decompress(packed)==raw,'Lossless history roundtrip');put(F/'history.json.gz',packed,'Exact text archive')
for d in history:need(hashlib.sha256(d['text'].encode()).hexdigest()==d['sha256'],'History text byte identity')
pin(plan['note']['path'],plan['note']['sha256']);copy(plan['note']['path'],Z/'rotation240_bootstrap.md')
for source,target in [(plan['review']['path'],F/'review/actual-review.json'),(review['reviewer_source']['path'],F/'review/review_actual.py'),(plan['batch']['path'],F/'provenance/batch.json'),(plan['driver']['path'],F/'provenance/batch-root.py'),(str(B/'inputs.json'),F/'publication/inputs.json'),(__file__,F/'publication/build_packet.py')]:copy(source,target)
need(all(sha(p)==h for p,h in tracked.items()),'Inputs changed during metadata publication')
publication=dict(status='ACTUAL_ROTATION240_BOOTSTRAP_PUBLICATION_PACKET',units=units,probes=72,callers=102,warnings=0,steps=409691,blocks=34,source_seconds=review['source_seconds'],audit_seconds=review['audit_seconds'],scope='Exact blank whole-tape prefix and activity through409691. Runtime frame, decoder coverage, binary consistency and internal PA remain separate.',proof_execution_by_publication=False,guard_bytes_unchanged=True,historical_cache_prerequisite=True,history_text_files=len(history),excluded=plan['excluded'],writer=desc(__file__),inputs=desc(B/'inputs.json'),review=plan['review'],files=[dict(path=p,sha256=hashlib.sha256(v[0]).hexdigest(),bytes=len(v[0])) for p,v in entries.items()])
put(Z/'results/rotation240-bootstrap-publication.json',enc(publication),'Publication metadata')
out.mkdir();mapping=[]
for path,(data,origin) in entries.items():
 target=out/'files'/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);need(target.read_bytes()==data,'Staged byte roundtrip')
 mapping.append(dict(path=path,packet_path=str(target),sha256=sha(target),bytes=len(data),origin=origin))
(out/'map.json').write_bytes(enc(mapping));(out/'publication.json').write_bytes(enc(publication))
print(json.dumps(dict(map=desc(out/'map.json'),publication=desc(out/'publication.json'),files=len(mapping),history_files=len(history)),indent=2))
