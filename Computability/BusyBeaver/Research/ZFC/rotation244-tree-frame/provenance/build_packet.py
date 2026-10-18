#!/usr/bin/env python3
"""Package two existing actual TreeRotation244/frame passes, without execution."""
from pathlib import Path
import argparse,hashlib,json,re
STANDARD={'propext','Classical.choice','Quot.sound'}
COMPILED=('.olean','.ilean','.olean.server','.olean.private','.o','.so','.a','.pyc','.c')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def desc(p):return dict(path=str(Path(p).resolve()),sha256=sha(p),bytes=Path(p).stat().st_size)
def load(p):return json.loads(Path(p).read_text())
def dump(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True)
 ap.add_argument('--output',type=Path,required=True);ap.add_argument('--units',type=Path,required=True)
 ap.add_argument('--units-sha',required=True);args=ap.parse_args();need(__debug__,'No optimized Python.')
 R,O,M=args.repo.resolve(),args.output.resolve(),args.units.resolve()
 need(sha(M)==args.units_sha,'Changed manifest.');m=load(M);rows=m['units']
 need(m['status']=='COMPLETE_ACTUAL_TREE_AND_FRAME'and len(rows)==2,'Wrong completed unit manifest.')
 roots=[Path(row['root']).resolve()for row in rows]
 need(roots==[Path('/tmp/zfc-tree-rotation244'),Path('/tmp/zfc-rotation244-frame')],'Wrong captured roots.')
 need(not O.exists()and not O.is_relative_to(R)and all(not O.is_relative_to(p)for p in roots),'Fresh external output required.')
 expected=[('BusyBeaver.ZFC.TreeRotation244','tree-rotation244',8,10,6),('BusyBeaver.ZFC.BootstrapFrameRotation244','rotation244-bootstrap-frame',8,9,125)]
 current={};units=[]
 def pin(p,h):
  p=Path(p).resolve();need(p.is_file()and sha(p)==h,'Changed input '+str(p))
  need(str(p)not in current or current[str(p)]==h,'Conflicting path binding.');current[str(p)]=h
 for row,root,(module,slug,probes,callers,providers)in zip(rows,roots,expected):
  need((row['module'],row['slug'])==(module,slug),'Wrong unit identity.')
  for key in ['record','source','audit','guard','preparation','review']:pin(row[key]['path'],row[key]['sha256'])
  E=Path(row['record']['path']).resolve();e=load(E);need(E==root/'run1/verification.json','Wrong actual path.')
  need(e['status']=='PASS'and e['prepare_only']is False and e['before']==e['after'],'Incomplete actual record.')
  need(all(e[k]for k in ['only_standard_axioms','source_object_recorded_before_audit','all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit']),'Missing postchecks.')
  for p,h in e['before'].items():pin(p,h)
  need(e['before'][str(Path(row['guard']['path']).resolve())]==row['guard']['sha256'],'Wrong executed guard.')
  for key in ['source','audit']:
   need(e[key]['sha256']==row[key]['sha256'],'Selected source/audit differs.');pin(e[key]['path'],row[key]['sha256']);pin(e[key]['snapshot'],row[key]['sha256'])
  f,=e['fresh_modules'];need(f['module']==module and f['source_sha256']==row['source']['sha256'],'Wrong fresh module.')
  pin(f['path'],f['sha256']);need(e['source_pass_object']==dict(f,source_command_index=0),'Wrong pre-audit capture.')
  ff=e['fresh_first_provider_before_audit'];need(ff['module']==module and ff['sha256']==f['sha256']and Path(ff.get('actual_first',ff.get('path'))).resolve()==Path(f['path']).resolve(),'Wrong fresh first provider.')
  actual={q['module']:q for q in e['actual_first_providers']};need(len(e['reused_modules'])==providers,'Wrong imported provider census.')
  for q in e['reused_modules']+e['toolchain_providers']:
   if 'source'in q:pin(q['source'],q['source_sha256'])
   pin(q['object'],q['object_sha256']);a=actual.get(q['module'],q)
   need(Path(a['actual_first']).resolve()==Path(q['object']).resolve()and a.get('sha256',a.get('object_sha256'))==q['object_sha256'],'Wrong actual first provider.')
  need([c['label']for c in e['commands']]==['source','audit'],'Wrong command order.')
  for c in e['commands']:
   need(c['exit_code']==0 and not c['timed_out']and c['interrupted']is None,'Failed source/audit.')
   need(c['command'][:3]==[e['compiler']['path'],'-j1','-M4096']and c['command'][3]=='--root='+str(E.parent/'sources')and c['command'][-1]==e[c['label']]['snapshot'],'Changed compiler command.')
   raw=E.parent/(c['label']+'.log');need(raw.read_text()==c['output']and 'warning:'not in c['output']and 'sorryAx'not in c['output'],'Raw output or warning differs.');pin(raw,sha(raw))
  need(e['commands'][0]['command'][4:6]==['-o',f['path']]and len(e['commands'][1]['command'])==5,'Wrong source/audit object action.')
  need(sum(c['seconds']for c in e['commands'])<120 and not e['dependency_build']and not e['downloads']and not e['compiler_version_query_performed'],'Changed resource policy.')
  if row['key']=='tree':need(e['shared_timeout_seconds']==120 and e['LEAN_NUM_THREADS']=='1'and e['memory_mebibytes']==4096 and e['global_option_overrides']==[]and e['warnings']==0,'Tree budget/warnings changed.')
  else:need(e['limits']==dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults')and e['warnings']==dict(source=0,audit=0),'Frame budget/warnings changed.')
  audit=Path(e['audit']['path']).read_text();names=re.findall(r'^#print axioms (\S+)$',audit,re.M)
  raw=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",e['commands'][1]['output'],re.M)
  rr=[dict(name=n,axioms=sorted({x.strip()for x in block.split(',')if x.strip()}))for n,block in raw]
  actual_rr=e.get('axiom_reports',e.get('actual_axiom_sets'))
  need(rr==[dict(name=q['name'],axioms=sorted(q['axioms']))for q in actual_rr]and [q['name']for q in rr]==names and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong exact named reports.')
  need((len(names),len(re.findall(r'^example\b',audit,re.M)))==(probes,callers)==(e['named_axiom_probes'],e['callers']),'Wrong audit census.')
  prep=load(row['preparation']['path']);need(prep['status']=='PREPARED_NOT_BUILT'and prep['prepare_only']and prep['commands']==[]and prep['fresh_modules']==[]and prep['before']==prep['after'],'Preparation promoted or changed.')
  for p,h in prep['before'].items():pin(p,h)
  review=load(row['review']['path']);need(review['status']=='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS'and review['findings']==[]and review['verification']['sha256']==row['record']['sha256'],'Wrong actual review.')
  for key in ['source','audit','guard']:need(review[key]['sha256']==row[key]['sha256'],'Review binding differs.')
  units.append(dict(row,probes=probes,callers=callers,providers=providers,actual_seconds={c['label']:c['seconds']for c in e['commands']},fresh_object=f))
 need((sum(x['probes']for x in units),sum(x['callers']for x in units))==(16,19)==(m['total_probes'],m['total_callers']),'Wrong total census.')
 for q in m['extra_history']+[m['note'],m['independent_tree_source_review']]:pin(q['path'],q['sha256'])
 peer=load(m['independent_tree_source_review']['path']);need(peer['findings']==[]and peer['tree_source']['sha256']==rows[0]['source']['sha256']and peer['tree_audit']['sha256']==rows[0]['audit']['sha256'],'Wrong independent tree source receipt.')
 extras={Path(q['path']).resolve()for q in m['extra_history']}|{M,Path(m['note']['path']).resolve(),Path(__file__).resolve(),Path(__file__).with_name('plan.md'),Path(__file__).with_name('prepare_manifest.py')}
 def paths():return sorted(set(p for root in roots for p in root.rglob('*')if p.is_file()or p.is_symlink())|extras,key=str)
 initial=paths();captured={};aliases=[];blobs={};excluded=[]
 for p in initial:
  if p.is_symlink():excluded.append(dict(path=str(p),kind='cache_symlink_not_copied',target=str(p.resolve()),sha256=sha(p)if p.is_file()else None));continue
  raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();captured[str(p)]=h
  if any(p.name.endswith(s)for s in COMPILED):excluded.append(dict(path=str(p),kind='compiled_not_copied',sha256=h,bytes=len(raw)));continue
  try:text=raw.decode('utf-8')
  except UnicodeDecodeError:excluded.append(dict(path=str(p),kind='non_utf8_not_copied',sha256=h,bytes=len(raw)));continue
  blobs.setdefault(h,dict(bytes=len(raw),utf8=text));aliases.append(dict(path=str(p),sha256=h,bytes=len(raw)))
 for q in aliases:need(blobs[q['sha256']]['utf8'].encode()==Path(q['path']).read_bytes(),'History roundtrip differs.')
 O.mkdir();Q=R/'Computability/BusyBeaver/Research/ZFC';L=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC';F=Q/'rotation244-tree-frame';files=[];destinations=set()
 def stage_bytes(raw,dst,original=None):
  need(dst not in destinations,'Duplicate target.');destinations.add(dst);p=O/'files'/str(len(files))/dst.name;p.parent.mkdir(parents=True);p.write_bytes(raw)
  files.append(dict(source=str(p),destination=str(dst),original=str(original)if original else None,sha256=sha(p),bytes=len(raw)))
 def stage(src,dst):stage_bytes(Path(src).read_bytes(),dst,src)
 for u in units:
  name=u['module'].rsplit('.',1)[1];P=Path(u['record']['path'])
  stage(u['source']['path'],L/(name+'.lean'));stage(u['audit']['path'],F/'audits'/(name+'Audit.lean'))
  stage(P,Q/'results'/(u['slug']+'-verification.json'));stage(u['guard']['path'],F/'provenance'/(name+'-check.py'))
  stage(u['preparation']['path'],F/'records'/(name+'-prepared.json'));stage(u['review']['path'],F/'reviews'/(name+'-actual-review.json'))
  for label in ['source','audit']:stage(P.parent/(label+'.log'),F/'logs'/(name+'-'+label+'.log'))
 tree=roots[0]
 for src,name in [(tree/'generated-v1/source-inventory.json','tree-inventory.json'),(tree/'generated-v1/tree-data.json','tree-data.json'),(tree/'boundary.json','tree-boundary.json'),(roots[1]/'source-inventory.json','frame-source-inventory.json'),(roots[1]/'guard-proposal.json','frame-guard-proposal.json')]:stage(src,F/'provenance'/name)
 stage(tree/'prepare_source.py',F/'provenance/prepare_tree_source.py');stage(tree/'Audit-template.lean',F/'provenance/Audit-template.lean')
 stage(m['independent_tree_source_review']['path'],F/'reviews/independent-tree-source-review.json')
 stage(M,F/'completed-units.json');stage(Path(__file__),F/'provenance/build_packet.py');stage(Path(__file__).with_name('plan.md'),F/'provenance/publication-plan.md')
 hp=O/'history.json';dump(hp,dict(schema='exact_utf8_history_v1',roots=[str(p)for p in roots],aliases=aliases,blobs=blobs,excluded=excluded));stage(hp,F/'history.json')
 replay='''These two existing Lean PASSES establish the exact rotated source tree and complete blank-start frame. Complete decoder coverage and final binary calibration remain separate. No internal PA endpoint is claimed.\n\nOriginal guards retain exact historical scratch/provider paths and actual parent records; no portable-default wrapper is supplied. The tree emitter and its Audit-template.lean are preserved together; --repo and a fresh external --output are required to generate source, which then needs fresh kernel checking. No proof, simulation, generator, version query or dependency build is performed by this packager. All selected cached provider pairs were checked, but are not copied, so this is not a clean-checkout rebuild.\n\nEvery UTF-8 history alias is recoverable as history.blobs[sha256].utf8 encoded as UTF-8. Compiled files and cache symlinks have explicit exclusion records. Source-only pending labels and the independent pilot-author receipt retain their original scope. The peer receipt's pilot emitter is included solely as provenance, not as another proved unit.\n'''
 stage_bytes(replay.encode(),F/'REPLAY.md');stage(m['note']['path'],Q/'rotation244_tree_frame.md')
 pub=dict(status='PASS_EXISTING_ROTATION244_TREE_FRAME_PUBLICATION',units=units,total_modules=2,total_probes=16,total_callers=19,warnings=0,manifest=desc(M),builder=desc(__file__),history=dict(sha256=sha(hp),aliases=len(aliases),blobs=len(blobs),excluded=len(excluded)),independent_tree_source_review=m['independent_tree_source_review'],proof_execution=False,generator_execution=False,maintained_writes=False,compiled_objects_published=False)
 pp=O/'publication.json';dump(pp,pub);stage(pp,Q/'results/rotation244-tree-frame-publication.json')
 need(initial==paths(),'Captured tree changed during packaging.')
 for p,h in captured.items():need(sha(p)==h,'Captured input changed '+p)
 for p,h in current.items():need(sha(p)==h,'Actual selected input changed '+p)
 for q in files:need(sha(q['source'])==q['sha256'],'Staged bytes changed.')
 dump(O/'map.json',dict(files=files,history=desc(hp),publication=desc(pp),proof_execution=False,maintained_writes=False))
 print(json.dumps(dict(map=desc(O/'map.json'),files=len(files),modules=2,probes=16,callers=19),indent=2))
if __name__=='__main__':main()
