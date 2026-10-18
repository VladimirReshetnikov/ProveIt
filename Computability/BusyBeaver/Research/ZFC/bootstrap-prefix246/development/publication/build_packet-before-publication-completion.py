#!/usr/bin/env python3
"""Package existing successful exact246 evidence; no proof or version execution."""
from pathlib import Path
import argparse,hashlib,json,re,shutil
B=Path(__file__).resolve().parents[1];R=Path('/home/codex/.codex/worktrees/ec20/Proofs');Z=R/'Computability/BusyBeaver/Research/ZFC';L=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.resolve();need(not out.is_relative_to(R) and not out.exists(),'New external output directory required.')
 units=[('probe16384',B.parent/'bootstrap-probe16384')]+[(f'group{i:02}',B/f'group{i:02}') for i in range(1,9)]
 parsed=[]
 # Validate everything before creating publication files.
 for name,base in units:
  rec=base/'run1/verification.json';r=json.loads(rec.read_text());need(r['status']=='PASS' and r['only_standard_axioms'] and r['source_object_recorded_before_audit'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit'],name+' incomplete')
  need(r['before']==r['after'],name+' stale input record')
  for path,h in r['before'].items():need(sha(Path(path))==h,'Current input mismatch '+path)
  for kind in ['source','audit']:need(sha(Path(r[kind]['path']))==sha(Path(r[kind]['snapshot']))==r[kind]['sha256'],'Snapshot mismatch')
  need([c['label'] for c in r['commands']]==['source','audit'] and all(c['exit_code']==0 for c in r['commands']),'Command mismatch')
  for c in r['commands']:need(Path(c['log']).read_text()==c['output'],'Log mismatch')
  for f in r['fresh_modules']:need(sha(Path(f['path']))==f['sha256'],'Fresh object changed')
  for f in r['actual_first_providers']:need(Path(f['actual_first']).resolve()==Path(f['resolved']) and sha(Path(f['actual_first']))==f['sha256'],'First provider changed')
  parsed.append((name,base,rec,r))
 out.mkdir();registry={};filemap=[];bindings={}
 def add(src,target,aliases=()):
  src=Path(src);h=sha(src);rel=str(target.relative_to(R));binding=dict(path=rel,sha256=h)
  if h in registry:
   need(registry[h]['bytes']==src.read_bytes(),'Hash collision')
   registry[h]['aliases'].update([str(src),*map(str,aliases)]);return dict(path=registry[h]['published_path'],sha256=h)
  dest=out/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
  registry[h]=dict(bytes=src.read_bytes(),published_path=rel,aliases={str(src),*map(str,aliases)})
  filemap.append(dict(source=str(dest),target=str(target),sha256=h));bindings[rel]=h;return binding
 programs=Z/'bootstrap-prefix246/programs'
 shared={n:add(B/n,programs/n) for n in ['generate.py','check-template.py']}
 shared['probe_generator']=add(B.parent/'bootstrap-probe16384/generate.py',programs/'generate_probe16384.py')
 entries=[]
 for name,base,rec,r in parsed:
  md=Z/'bootstrap-prefix246/modules'/name;ad=Z/'bootstrap-prefix246/attempts'/name/'run1'
  src=Path(r['source']['path']);aud=Path(r['audit']['path'])
  artifacts=dict(source=add(src,L/src.name,[r['source']['snapshot']]),audit=add(aud,md/'Audit.lean',[r['audit']['snapshot']]),executed_guard=add(base/'check.py',md/'executed-check.py'),data=add(base/'data.json',md/'data.json'),verification=add(rec,ad/'verification.json'))
  for c in r['commands']:artifacts[c['label']+'_log']=add(Path(c['log']),ad/(c['label']+'.log'))
  for extra in ['source-inventory.json','author-source-review.json','author-static-review.json','finish-frame-data-review.json']:
   if (base/extra).exists():artifacts[extra]=add(base/extra,md/extra)
  reviews=[]
  if (base/'review').exists():
   for q in sorted((base/'review').glob('*')):
    if q.is_file():reviews.append(add(q,Z/'bootstrap-prefix246/reviews'/name/q.name))
  reported_events=[]
  for q in sorted((base/'history').glob('*root-report.json')) if (base/'history').exists() else []:
   reported_events.append(add(q,Z/'bootstrap-prefix246/development'/name/q.name))
  for key in ['source','audit']:
   for q in sorted((base/'history').glob('**/'+Path(r[key]['path']).name)) if (base/'history').exists() else []:
    if sha(q)==r[key]['sha256']:registry[r[key]['sha256']]['aliases'].add(str(q))
  entries.append(dict(name=name,status='PASS',module=r['fresh_modules'][0]['module'],scope=r['scope'],record_sha256=sha(rec),parent_evidence=r['parent_evidence'],artifacts=artifacts,independent_reviews=reviews,reported_precompiler_events=reported_events,actual_axiom_sets=r['actual_axiom_sets'],warnings=r['warnings'],commands=[dict(label=c['label'],seconds=c['seconds'],exit_code=c['exit_code']) for c in r['commands']],fresh_module=r['fresh_modules'][0],reused_modules=r['reused_modules'],toolchain_providers=r['toolchain_providers']))
 development=[]
 for q in sorted((B.parent/'bootstrap-probe16384/development').glob('*')):
  if q.is_file():development.append(add(q,Z/'bootstrap-prefix246/development'/q.name))
 first=Z/'results/boot-prefix246-first-verification.json';need(sha(first)=='15f05525b6910028930b4fc22b7e89f00967bbca7cede98b56597b79ae648b95','Published First record changed')
 # All registered aliases point to the exact stored bytes. Binary providers remain explicit prerequisites.
 reg={h:dict(published_path=v['published_path'],original_aliases=sorted(v['aliases'])) for h,v in sorted(registry.items())}
 manifest=dict(status='EXACT_COMPLETED_BOOTSTRAP_EVIDENCE_PACKET',target='machinePrefix246',blank_endpoint=410735,canonical_table_sha256='89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc',final_theorem='SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk008.bootstrap410735',first_checkpoint=dict(path=str(first.relative_to(R)),sha256=sha(first)),units=entries,shared_programs=shared,development_events=development,content_registry=reg,all_current_inputs_rechecked=True,no_compiler_or_checker_or_version_invocation=True,objects_not_published=True,scope='Complete blank-run state/head/infinite tape at410735 and no earlier halt. Dispatch interpretation, arbitrary runtime and consistency endpoints remain separate.',reproduction_status='Exact executed guards preserved as history; portable replay recipe is separate.')
 mp=out/'manifest.json';dump(mp,manifest);filemap.append(dict(source=str(mp),target=str(Z/'bootstrap-prefix246/manifest.json'),sha256=sha(mp)))
 dump(out/'file-map.json',filemap);print(json.dumps(dict(files=len(filemap),manifest_sha256=sha(mp),map_sha256=sha(out/'file-map.json')),indent=2))
if __name__=='__main__':main()
