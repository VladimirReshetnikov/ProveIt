#!/usr/bin/env python3
"""Publish only the explicit frozen three-unit snapshot to a fresh external packet."""
from pathlib import Path
import argparse,hashlib,json,re,ast,difflib
B=Path('/tmp/zfc-source-rotation244-publication-design')
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
Z=Path('Computability/BusyBeaver/Research/ZFC');L=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
INPUT_SHA='891031ad3def3af7d1e2613c53f6b9296f8684de99ee59a46621cb28a155f309'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return dict(path=str(p),sha256=sha(p))
def need(x,msg):
 if not x:raise RuntimeError(msg)
def load(p):return json.loads(Path(p).read_text())
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output.resolve()
need(not out.exists() and not out.is_relative_to(ROOT) and not out.is_relative_to(B),'Fresh external packet required')
need(sha(B/'inputs.json')==INPUT_SHA,'Changed explicit snapshot');plan=load(B/'inputs.json');tracked={};cooked={};actual={}
def pin(path,h):
 path=Path(path).resolve();need(sha(path)==h,'Changed '+str(path));need(str(path) not in tracked or tracked[str(path)]==h,'Conflicting identity');tracked[str(path)]=h
for u in plan['units']:
 base=Path(u['base']);v=u['verification'];pin(v['path'],v['sha256']);r=load(v['path']);n=u['probes'];k=u['callers']
 need(r['status']=='PASS' and not r['prepare_only'] and (r['named_axiom_probes'],r['callers'],r['warnings'])==(n,k,0),'Actual status/census')
 need(r['before']==r['after'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit'] and r['only_standard_axioms'],'Actual postchecks')
 for path,h in r['before'].items():pin(path,h)
 need(r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1' and r['global_option_overrides']==[],'Resource defaults')
 need(not any(r[x] for x in ['compiler_version_query_performed','dependency_build','downloads']),'Unexpected side execution')
 need(len(r['reused_modules'])==r['exact_project_prerequisite_count']==u['projects'],'Project census')
 need([c['label'] for c in r['commands']]==['source','audit'],'Sequential proof pair')
 for i,c in enumerate(r['commands']):
  need(c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None,'Failed command')
  need(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'] and c['command'][-1]==r[['source','audit'][i]]['snapshot'],'Command selection')
  pin(c['log'],c['log_sha256']);need(Path(c['log']).read_text()==c['output'],'Raw log mismatch')
 need(sum(c['seconds'] for c in r['commands'])<120,'Shared deadline')
 for x in ['source','audit']:pin(r[x]['path'],r[x]['sha256']);pin(r[x]['snapshot'],r[x]['sha256'])
 need(Path(r['source']['path']).resolve()==base/(u['module']+'.lean') and Path(r['audit']['path']).resolve()==base/'Audit.lean','Exact source/audit paths')
 f=r['fresh_modules'];need(len(f)==1,'Single fresh target');f=f[0];pin(f['path'],f['sha256'])
 need(f['module']=='BusyBeaver.ZFC.'+u['module'] and f['source_sha256']==r['source']['sha256'],'Fresh source binding')
 need(r['source_object_recorded_before_audit'] and r['source_pass_object']==dict(f,source_command_index=0) and r['fresh_first_provider_before_audit']=={x:f[x] for x in ['module','path','sha256']},'Pre-audit capture')
 names=re.findall(r'^#print axioms (\S+)$',Path(r['audit']['path']).read_text(),re.M)
 need(names==[q['name'] for q in r['axiom_reports']] and len(names)==n and len(re.findall(r'^example\b',Path(r['audit']['path']).read_text(),re.M))==k,'Typed audit census')
 need(all(set(q['axioms'])<={'propext','Quot.sound','Classical.choice'} for q in r['axiom_reports']),'Axiom scope')
 pin(u['review']['path'],u['review']['sha256']);rv=load(u['review']['path'])
 need(rv['status']=='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS' and rv['findings']==[] and rv['verification']==v,'Exact existing review')
 for x in ['source','audit']:need(rv[x]==d(r[x]['path']),'Reviewed proof identity')
 need(rv['guard']==d(base/'check.py'),'Reviewed guard identity');pin(rv['reviewer_source']['path'],rv['reviewer_source']['sha256'])
 need(r['before'].get(str(base/'check.py'))==sha(base/'check.py'),'Executed guard exact')
 for q in u['files']:
  need(Path(q['relative']).parts[0]!='cache' and not Path(q['path']).is_symlink(),'No compiled/symlinked cache')
  need(Path(q['path']).resolve()==base/q['relative'],'Snapshot path binding');pin(q['path'],q['sha256']);Path(q['path']).read_bytes().decode('utf-8')
 pr=load(base/'prepared1/verification.json');need(pr['status']=='PREPARED_NOT_BUILT' and pr['commands']==pr['fresh_modules']==[] and pr['before']==pr['after'],'Preparation scope')
 raw=(base/'check.py').read_text();s=raw
 changes=[("HERE=Path('"+str(base)+"')",'HERE=Path(__file__).resolve().parent\nREPO=HERE.parents[3]'),("default=HERE/'"+u['module']+".lean'","default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/"+u['module']+".lean'"),("default=HERE/'Audit.lean'","default=HERE/'"+u['stem']+"_audit.lean'"),("default=HERE/'boundary.json'","default=HERE/'source-rotation244-formal/"+u['slug']+"/boundary.json'")]
 for before,after in changes:need(s.count(before)==1,'Default occurrence');s=s.replace(before,after)
 inverse=s
 for before,after in reversed(changes):need(inverse.count(after)==1,'Default inverse occurrence');inverse=inverse.replace(after,before)
 need(inverse==raw,'Only path defaults may differ');ast.parse(s);cooked[u['slug']]=(s,''.join(difflib.unified_diff(raw.splitlines(True),s.splitlines(True),fromfile='executed-check.py',tofile='maintained-check.py')));actual[u['slug']]=v
pin(plan['note']['path'],plan['note']['sha256'])
# No source-tree glob occurs here: only the immutable completed-unit file list is used.
out.mkdir();files=[];targets=set()
def put(target,data,origin):
 need(not target.is_absolute() and '..' not in target.parts and str(target) not in targets,'Unsafe/duplicate target');targets.add(str(target))
 dst=out/'files'/target;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 files.append(dict(path=str(target),packet_path=str(dst),sha256=sha(dst),bytes=len(data),origin=origin))
def copy(src,target):put(target,Path(src).read_bytes(),str(src))
for u in plan['units']:
 base=Path(u['base']);arc=Z/'source-rotation244-formal'/u['slug']
 for q in u['files']:copy(q['path'],arc/q['relative'])
 copy(base/(u['module']+'.lean'),L/(u['module']+'.lean'));copy(base/'Audit.lean',Z/(u['stem']+'_audit.lean'))
 text,delta=cooked[u['slug']];put(Z/('check_'+u['stem']+'.py'),text.encode(),'Maintained path defaults only');put(arc/'publication-defaults.diff',delta.encode(),'Exact default-only inverse')
 copy(u['verification']['path'],Z/'results'/('source-rotation244-'+u['slug']+'-verification.json'))
copy(plan['note']['path'],Z/'source_rotation244.md')
copy(B/'inputs.json',Z/'source-rotation244-formal/publication/inputs.json');copy(__file__,Z/'source-rotation244-formal/publication/build_packet.py')
need(all(sha(path)==h for path,h in tracked.items()),'Inputs changed during metadata publication')
manifest=dict(status='THREE_COMPLETED_SOURCE_ROTATION_UNITS_PACKET',proof_execution=False,writer=d(__file__),inputs=d(B/'inputs.json'),actual_records=actual,probes=18,callers=21,warnings=0,scope='Concrete two-row interface plus generic local/context lemmas only; concrete whole-source/WF/path and binary calibration remain separate.',files=files)
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(out/'map.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps(dict(files=len(files),manifest=d(out/'manifest.json'),map=d(out/'map.json')),indent=2))
