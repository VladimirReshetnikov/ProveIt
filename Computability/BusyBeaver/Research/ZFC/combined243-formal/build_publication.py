#!/usr/bin/env python3
"""Create an external publication packet from five actual checked units; no proof execution."""
from pathlib import Path
import argparse,hashlib,json,re,ast,difflib
B=Path('/tmp/zfc243-combined-lean')
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
Z=Path('Computability/BusyBeaver/Research/ZFC');L=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p):return dict(path=str(p),sha256=sha(p))
def need(x,msg):
 if not x:raise RuntimeError(msg)
def load(p):return json.loads(Path(p).read_text())
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
parser.add_argument('--simulation-record',type=Path,required=True)
parser.add_argument('--simulation-sha',required=True)
parser.add_argument('--simulation-review',type=Path,required=True)
parser.add_argument('--simulation-review-sha',required=True)
a=parser.parse_args();out=a.output.resolve()
need(not out.exists(),'Fresh packet directory required.')
need(not out.is_relative_to(ROOT) and not out.is_relative_to(B),'External packet outside source tree required.')
units=[
 ('table-rotation','table_rotation244','TableRotation244','run2','check-v2.py',7,7,1,'339ac1eb684bf2b0e2dca81f6a5d693abf2f3fe7079d0c924e5cf2ab870f3466','table-rotation-independent-actual-review.json'),
 ('table-combined','table_combined243','TableCombined243','run1','check.py',53,6,2,'3aa2fbcd854242ec36086af6cce69ad8b0e00c949f8c2d67a5c28dd025cb175d','table-combined-independent-actual-review.json'),
 ('invariant','rotation244_invariant','Rotation244Invariant','run1','check.py',5,8,2,'76cf8e6e038f187b336908c860227375eb5bfdfbdd6a52e644ef7c18ec03c6d0','invariant-actual-evidence-review.json'),
 ('blocks','combined243_blocks','Combined243Blocks','run1','check.py',14,14,3,'e4ebb3fcf294760563409069fae6211593bd7fcbd07b428438819db1fc684cb7','blocks-actual-evidence-review.json'),
 ('simulation','combined243_simulation','Combined243Simulation','run1','check.py',4,4,7,a.simulation_sha,None)]
inventory=load(B/'source-inventory.json');byname={u['name']:u for u in inventory['units']}
records={};reviews={};inputs={};prepared={}
def pin(path,h=None):
 path=Path(path).resolve();v=sha(path);need(h is None or v==h,'Changed '+str(path))
 need(str(path) not in inputs or inputs[str(path)]==v,'Conflicting input '+str(path));inputs[str(path)]=v;return path
for slug,stem,module,run,guard,np,nc,nproj,h,reviewname in units:
 u=B/slug;p=a.simulation_record if slug=='simulation' else u/run/'verification.json';pin(p,h);r=load(p)
 need(r['status']=='PASS' and not r['prepare_only'] and (r['named_axiom_probes'],r['callers'],r['warnings'])==(np,nc,0),'Wrong actual result '+slug)
 need(r['before']==r['after'] and r['all_input_provider_postchecks'] and r['only_standard_axioms'] and r['all_fresh_objects_unchanged_after_audit'],'Incomplete postchecks '+slug)
 need(r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1' and r['global_option_overrides']==[],'Wrong limits '+slug)
 need(not any(r[k] for k in ['compiler_version_query_performed','dependency_build','downloads']),'Unexpected side execution '+slug)
 for path,hv in r['before'].items():pin(path,hv)
 for k in ['source','audit']:
  pin(r[k]['path'],r[k]['sha256']);pin(r[k]['snapshot'],r[k]['sha256'])
 need(Path(r['source']['path']).resolve()==(u/(module+'.lean')).resolve() and Path(r['audit']['path']).resolve()==(u/'Audit.lean').resolve(),'Wrong selected proof paths '+slug)
 if module in byname:
  need(all(r[k]['sha256']==byname[module][k]['sha256'] for k in ['source','audit']),'Changed frozen port '+slug)
 need(r['exact_project_prerequisite_count']==len(r['reused_modules'])==nproj,'Wrong provider count '+slug)
 need([q['label'] for q in r['commands']]==['source','audit'],'Wrong command order '+slug)
 for i,c in enumerate(r['commands']):
  need(c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None,'Failed command '+slug)
  need(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'] and c['command'][-1]==r[['source','audit'][i]]['snapshot'],'Command flags/paths '+slug)
  pin(c['log'],c['log_sha256']);need(Path(c['log']).read_text()==c['output'],'Raw log changed '+slug)
 need(sum(c['seconds'] for c in r['commands'])<120,'Shared limit exceeded '+slug)
 f=r['fresh_modules'];need(len(f)==1,'Wrong fresh count '+slug);f=f[0]
 pin(f['path'],f['sha256']);need(f['module']=='BusyBeaver.ZFC.'+module and f['source_sha256']==r['source']['sha256'],'Fresh binding '+slug)
 need(r['source_object_recorded_before_audit'] and r['source_pass_object']==dict(f,source_command_index=0) and r['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']},'Missing pre-audit capture '+slug)
 names=re.findall(r'^#print axioms (\S+)$',Path(r['audit']['path']).read_text(),re.M)
 need(names==[q['name'] for q in r['axiom_reports']] and len(names)==np and len(re.findall(r'^example\b',Path(r['audit']['path']).read_text(),re.M))==nc,'Audit census '+slug)
 need(all(set(q['axioms'])<={'propext','Quot.sound','Classical.choice'} for q in r['axiom_reports']),'Nonstandard axioms '+slug)
 rp=a.simulation_review if slug=='simulation' else B/reviewname;pin(rp,a.simulation_review_sha if slug=='simulation' else None);rv=load(rp)
 need(rv['status']=='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS' and rv['findings']==[] and rv['verification']==desc(p),'Missing exact actual review '+slug)
 for k in ['source','audit']:need(rv[k]==desc(r[k]['path']),'Review proof mismatch '+slug)
 need(rv['guard']==desc(u/guard),'Review guard mismatch '+slug)
 pin(rv['reviewer_source']['path'],rv['reviewer_source']['sha256'])
 need(str((u/guard).resolve()) in r['before'] and r['before'][str((u/guard).resolve())]==sha(u/guard),'Executed guard mismatch '+slug)
 records[slug]=desc(p);reviews[slug]=desc(rp)
 pr=u/'prepared1/verification.json';pin(pr);pp=load(pr)
 need(pp['status']=='PREPARED_NOT_BUILT' and pp['commands']==pp['fresh_modules']==[] and pp['before']==pp['after'],'Preparation changed '+slug);prepared[slug]=desc(pr)
# Retain the actual initial rotation-table failure and exact mkdir-only successor.
old=B/'table-rotation/check.py';new=B/'table-rotation/check-v2.py'
need(old.read_text().replace("require(not obj.exists(),'Target already exists.');run('source',ss,obj)","require(not obj.exists(),'Target already exists.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)")==new.read_text(),'Unexpected rotation repair')
failed=B/'table-rotation/run1/verification.json';pin(failed);fr=load(failed)
need(fr['status']=='FAIL' and [q['label'] for q in fr['commands']]==['source'] and fr['fresh_modules']==[],'Lost failed attempt')
need('failed to write' in fr['commands'][0]['output'] and not fr['commands'][0]['timed_out'],'Wrong original failure')
# Snapshot the complete small source tree: all regular text artifacts, never caches/objects.
archive=[]
for path in sorted(B.rglob('*')):
 if not path.is_file() or path.is_symlink():continue
 rel=path.relative_to(B)
 if 'cache' in rel.parts or '__pycache__' in rel.parts:continue
 if path.suffix not in {'.lean','.json','.py','.diff','.log','.md','.txt'}:continue
 path.read_bytes().decode('utf-8');pin(path);archive.append((path,Z/'combined243-formal'/rel))
extras=[a.simulation_review,Path(load(a.simulation_review)['reviewer_source']['path']),Path('/tmp/zfc243-calibration-plan/dependent-guards-source-review.json')]
for path in extras:pin(path)
# All checks precede the first output. Only the fresh external packet is written.
files=[];targets=set();out.mkdir()
def put(target,data,origin):
 need(not target.is_absolute() and '..' not in target.parts and str(target) not in targets,'Unsafe/duplicate target')
 targets.add(str(target));dst=out/'files'/target;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 files.append(dict(path=str(target),packet_path=str(dst),sha256=sha(dst),bytes=len(data),origin=origin))
def copy(src,target):put(target,Path(src).read_bytes(),str(src))
for src,target in archive:copy(src,target)
for src in extras:
 if src.is_relative_to(B):continue
 target=Z/'combined243-formal/external-reviews'/src.name
 if str(target) not in targets:copy(src,target)
for slug,stem,module,run,guard,np,nc,nproj,h,reviewname in units:
 u=B/slug;copy(u/(module+'.lean'),L/(module+'.lean'));copy(u/'Audit.lean',Z/(stem+'_audit.lean'))
 raw=(u/guard).read_text();cooked=raw
 replacements=[("HERE=Path('"+str(u)+"')",'HERE=Path(__file__).resolve().parent\nREPO=HERE.parents[3]'),("default=HERE/'"+module+".lean'","default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/"+module+".lean'"),("default=HERE/'Audit.lean'","default=HERE/'"+stem+"_audit.lean'"),("default=HERE/'boundary.json'","default=HERE/'combined243-formal/"+slug+"/boundary.json'")]
 for before,after in replacements:need(cooked.count(before)==1,'Missing default '+slug);cooked=cooked.replace(before,after)
 inverse=cooked
 for before,after in reversed(replacements):need(inverse.count(after)==1,'Ambiguous default inverse');inverse=inverse.replace(after,before)
 need(inverse==raw,'Non-default guard change');ast.parse(cooked)
 put(Z/('check_'+stem+'.py'),cooked.encode(),'Maintained path defaults only from '+str(u/guard))
 delta=''.join(difflib.unified_diff(raw.splitlines(True),cooked.splitlines(True),fromfile=guard,tofile='check_'+stem+'.py'))
 put(Z/'combined243-formal'/slug/'publication-defaults.diff',delta.encode(),'Exact default-only guard delta')
 copy(records[slug]['path'],Z/'results'/('combined243-'+slug+'-verification.json'))
copy(B/'publication-note.md',Z/'combined243_simulation.md')
need(all(sha(path)==h for path,h in inputs.items()),'Input changed during metadata publication')
manifest=dict(status='FIVE_ACTUAL_CHECKED_UNITS_PUBLICATION_PACKET',proof_execution=False,publication_writer=desc(__file__),actual_records=records,actual_reviews=reviews,preparations=prepared,failed_rotation_attempt=desc(failed),scope='Relative Combined243/Rotation244 whole-run equivalence; no Lean consistency calibration or PA endpoint.',probes=83,callers=39,warnings=0,files=files,input_hashes=inputs,excluded=['compiled caches','symlinked providers','object files','dependency trees'])
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(out/'map.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps(dict(status=manifest['status'],files=len(files),manifest=desc(out/'manifest.json'),map=desc(out/'map.json')),indent=2))
