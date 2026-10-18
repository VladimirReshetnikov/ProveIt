#!/usr/bin/env python3
"""Serial routing245 leaf measurements, each with a shared120-second source/audit budget.

Uses exact successful SiteRouting245 and ProgramRouting245 providers. Each leaf
proves actual-tree linkage and acceptance at fuel4000; CD includes both guards.
No complete coverage, bootstrap or PA endpoint is claimed. No dependency build,
download or compiler/version call in prepare-only. Existing caches are required.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, time

HERE=Path(__file__).resolve().parent
MANIFEST_SHA='032d42a2d8d8de138482b025d7759d725139a3ed056ed25213b3af61a2e2e5f1'
GENERATOR_SHA='178c3e081ce28d4c684da47c84cb40407d148aeeeb3031a416c565d262468cc4'
PARENTS={
 'site':('/tmp/zfc-routing245-lean/site/run1/verification.json','c50747f277b2b9d9f732240e031fb9ef7d494bec5e4f9f24a1b5522ce124e746','BusyBeaver.ZFC.SiteRouting245',12,13),
 'program':('Computability/BusyBeaver/Research/ZFC/results/program-routing245-verification.json','1efd9f64fc8067e85518fc9968752a9a10f78cdeb4f24aa8dd9e8c58d2a53c71','BusyBeaver.ZFC.ProgramRouting245',11,13),
}
COMPILER_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
TOOLS={'Init':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e','Lean.Elab.Tactic.Omega':'eb766bae1ab40110a853c7cca853e36e1f4aece010a09fa4dd9b1b48116953fe'}
ORDER=[1704,1609,1703,1705,1720,4730,6324]
EXPECTED_CASES={1704:(51,'CI',1,1,3),1705:(51,'CC',2,1,3),1609:(42,'CD',2,2,5),1703:(50,'CD',6,2,5),1720:(47,'CB',1,1,3),4730:(35,'CC',2,1,3),6324:(13,'CH',None,1,3)}
DIRECT=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteRouting245']
PROBES=['actual_leaf','site_checked']
TIMEOUT=120

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise RuntimeError(m)
def imports(p):return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(p).read_text(),re.M)
def first_path(d):return Path(d['actual_first'] if 'actual_first' in d else d['path']).resolve()
def descriptor(p):return dict(path=str(p),sha256=sha(p))

def run_unit(args,plan,unit,work):
 repo=args.repo.resolve();manifest=args.manifest.resolve();generator=args.generator.resolve()
 module=unit['module'];prefix='SetTheory.BusyBeaver.ZFC.'+module.rsplit('.',1)[1]+'.'
 i=unit['site_index'];depth,opcode,operand,guards,callers=EXPECTED_CASES[i]
 need(not work.exists() and not work.is_relative_to(repo),'Use a fresh external unit output.')
 need(module==f'BusyBeaver.ZFC.SitesRouting245Pilot{i:04d}' and unit['depth']==depth and
      unit['opcode']==opcode and unit['operand']==operand and unit['guards']==guards and
      unit['probes']==2 and unit['callers']==callers and unit['imports']==DIRECT,'Unit descriptor differs.')
 source=Path(unit['source']['path']).resolve();audit=Path(unit['audit']['path']).resolve()
 inputs=[Path(__file__).resolve(),manifest,generator]
 for entry in plan['inputs']:
  p=Path(entry['path']).resolve();need(sha(p)==entry['sha256'],'Changed selected metadata input '+str(p));inputs.append(p)
 # Revalidate every frozen pilot source/audit, even when selecting one leaf.
 for entry in plan['pilots']:
  for role in ('source','audit'):
   p=Path(entry[role]['path']).resolve();need(sha(p)==entry[role]['sha256'],'Changed pilot '+str(p));inputs.append(p)
 need(sha(manifest)==MANIFEST_SHA and sha(generator)==GENERATOR_SHA,'Changed pilot manifest/emitter.')
 st,at=source.read_text(),audit.read_text()
 need(imports(source)==DIRECT and imports(audit)==[module],'Pilot imports differ.')
 need(re.findall(r'^theorem (\w+)',st,re.M)==PROBES,'Pilot theorem census differs.')
 need(re.findall(r'^#print axioms (\S+)$',at,re.M)==[prefix+n for n in PROBES] and
      len(re.findall(r'^example\b',at,re.M))==callers,'Pilot audit census differs.')
 for text in (st,at):
  need(not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s',text,re.M),'Forbidden proof shortcut.')
  need(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',text),'Keep default proof limits.')
 expected_path='['+', '.join('true' if b=='1' else 'false' for b in unit['path'])+']'
 expected_edge='.halt' if opcode=='CH' else '.'+{'CI':'inc','CD':'decnz','CB':'brk','CC':'cont'}[opcode]+' '+str(operand)
 need(f'def path : List Bool := {expected_path}\n' in st and f'def instruction : Edge := {expected_edge}\n' in st,
      'Literal source case differs from manifest.')
 selected={};evidence={};summaries=[];compiler=None;version=None;tool_pins={}
 def add(q,e):
  m=q['module'];s=Path(q['source']).resolve();o=Path(q['object']).resolve()
  need(sha(s)==q['source_sha256'] and sha(o)==q['object_sha256'],'Current provider changed '+m)
  row=dict(module=m,source=str(s),source_sha256=sha(s),object=str(o),object_sha256=sha(o),evidence=str(e))
  if m in selected:
   need((selected[m]['source_sha256'],selected[m]['object_sha256'])==(row['source_sha256'],row['object_sha256']),
        'Conflicting same-named provider '+m)
  else:selected[m]=row
 for label,(_,pin,parent_module,probes,parent_callers) in PARENTS.items():
  e=getattr(args,label+'_evidence').resolve();need(sha(e)==pin,'Changed '+label+' parent record')
  parent=json.loads(e.read_text());evidence[str(e)]=pin;inputs.append(e)
  need(parent['status']=='PASS' and parent['prepare_only'] is False and parent['only_standard_axioms'] is True and
       parent['all_input_provider_postchecks'] is True and parent['all_fresh_objects_unchanged_after_audit'] is True and
       parent['before']==parent['after'] and parent['source_object_recorded_before_audit'] is True,'Incomplete '+label+' parent')
  need((parent['named_axiom_probes'],parent['callers'])==(probes,parent_callers),'Parent audit census differs.')
  need([q['label'] for q in parent['commands']]==['source','audit'] and
       all(q['exit_code']==0 and not q.get('timed_out',False) for q in parent['commands']),'Parent command failure.')
  c=Path(parent['compiler']['path']).resolve()
  need(sha(c)==parent['compiler']['sha256']==COMPILER_SHA,'Compiler binding differs.')
  if compiler is None:compiler=c;version=parent['compiler']['version']
  else:need(compiler==c and version==parent['compiler']['version'],'Parent compiler identities differ.')
  actuals={q['module']:q for q in parent['actual_first_providers']}
  need(len(actuals)==len(parent['actual_first_providers'])==len(parent['reused_modules']),'Duplicate/missing parent providers.')
  for q in parent['reused_modules']:
   for k in ('source','object'):
    need(parent['before'][q[k]]==parent['after'][q[k]]==q[k+'_sha256'],'Parent reused input binding differs.')
   actual=actuals[q['module']]
   need(actual['sha256']==q['object_sha256'] and first_path(actual)==Path(q['object']).resolve(),'Parent actual provider differs.')
   add(q,e)
  fresh=parent['fresh_modules'];need(len(fresh)==1 and fresh[0]['module']==parent_module,'Wrong fresh parent module.')
  q=fresh[0];saved=parent['source_pass_object']
  need(all(saved[k]==q[k] for k in ('module','path','sha256','source_sha256')),'Parent pre-audit object binding differs.')
  for role in ('source','audit'):
   p=Path(parent[role]['path']).resolve();snap=Path(parent[role]['snapshot']).resolve()
   need(sha(p)==sha(snap)==parent[role]['sha256']==parent['before'][str(p)]==parent['after'][str(p)],'Parent source/audit snapshot differs.')
   inputs.extend([p,snap])
  s=Path(parent['source']['path']).resolve()
  need(q['source_sha256']==parent['source']['sha256'] and sha(q['path'])==q['sha256'],'Fresh parent source/object differs.')
  first=parent['fresh_first_provider_before_audit']
  need(first['module']==parent_module and first['sha256']==q['sha256'] and first_path(first)==Path(q['path']).resolve(),
       'Parent fresh first provider differs.')
  add(dict(module=parent_module,source=str(s),source_sha256=sha(s),object=q['path'],object_sha256=q['sha256']),e)
  summaries.append(dict(label=label,evidence=str(e),module=parent_module,source_object_recorded_before_audit=True,
                        source_sha256=sha(s),object_sha256=q['sha256']))
  for t in parent['toolchain_providers']:
   need(t['module'] in TOOLS and t['object_sha256']==TOOLS[t['module']] and sha(t['object'])==t['object_sha256'],'Parent tool boundary differs.')
   if t['module'] in tool_pins:need(tool_pins[t['module']]==t['object_sha256'],'Conflicting tool boundary.')
   tool_pins[t['module']]=t['object_sha256']
  for ref in parent.get('provider_evidence',parent.get('parent_evidence',[])):
   p=Path(ref['path']).resolve();need(sha(p)==ref['sha256'],'Parent provenance record changed.');evidence[str(p)]=ref['sha256'];inputs.append(p)
 need(tool_pins==TOOLS,'Exact Init/Omega tool boundary differs.')
 site_source=Path(selected['BusyBeaver.ZFC.SiteRouting245']['source'])
 need(re.search(r'^def minDistance : Nat := 64$',site_source.read_text(),re.M) and
      re.search(r'^def fuel : Nat := 4000$',site_source.read_text(),re.M),'Site margin/fuel differs.')
 visiting=set();closure=[];tool_names={'Init'}
 def visit(m):
  if m in closure:return
  need(m in selected and m not in visiting,'Missing/cyclic provider '+m);visiting.add(m)
  for n in imports(selected[m]['source']):
   if n=='Init' or n.startswith(('Lean.','Std.')):tool_names.add(n)
   else:visit(n)
  visiting.remove(m);closure.append(m)
 for m in DIRECT:visit(m)
 need(set(closure)==set(selected) and len(closure)==22,'Exact22-project closure differs.')
 need(tool_names==set(TOOLS),'Unexpected tool boundary.')
 toolroot=compiler.parent.parent/'lib/lean'
 inputs.append(compiler)
 for q in selected.values():inputs.extend([Path(q['source']),Path(q['object'])])
 for m,pin in TOOLS.items():
  p=toolroot/Path(m.replace('.','/')).with_suffix('.olean');need(sha(p)==pin,'Selected compiler library differs.');inputs.append(p)
 for p in inputs:need(not p.is_relative_to(work),'Input lies in unit output.')
 work.mkdir(parents=True);cache=work/'cache';cache.mkdir();snap=work/'sources'
 ss=snap/Path(module.replace('.','/')).with_suffix('.lean');ss.parent.mkdir(parents=True)
 aa=snap/'Audit.lean';shutil.copyfile(source,ss);shutil.copyfile(audit,aa)
 for m in closure:
  dst=cache/Path(m.replace('.','/')).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(selected[m]['object'])
 def first(m):
  rel=Path(m.replace('.','/')).with_suffix('.olean')
  return next(p/rel for p in (cache,toolroot) if (p/rel).is_file())
 actual=[]
 for m in closure:
  p=first(m);need(p.resolve()==Path(selected[m]['object']).resolve() and sha(p)==selected[m]['object_sha256'],'Actual first provider differs.')
  actual.append(dict(module=m,actual_first=str(p),resolved=str(p.resolve()),sha256=sha(p)))
 tools=[]
 for m,pin in TOOLS.items():
  p=first(m);expected=toolroot/Path(m.replace('.','/')).with_suffix('.olean')
  need(p.resolve()==expected.resolve() and sha(p)==pin,'Actual tool provider differs.')
  tools.append(dict(module=m,object=str(expected),object_sha256=pin,actual_first=str(p)))
 inputs.extend([ss,aa]);inputs=list(dict.fromkeys(p.resolve() for p in inputs));before={str(p):sha(p) for p in inputs}
 env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',LEAN_SYSROOT=str(compiler.parent.parent),PYTHONDONTWRITEBYTECODE='1')
 record=dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',prepare_only=args.prepare_only,scope=__doc__,
  leaf_index=i,path_bits=unit['path'],depth=depth,opcode=opcode,operand=operand,guard_cases=guards,site_fuel=4000,margin=64,
  compiler=dict(path=str(compiler),version=version,sha256=sha(compiler),compiler_version_query_performed=False),compiler_version_query_performed=False,
  source_overridden=False,audit_overridden=False,source=dict(path=str(source),sha256=sha(source),snapshot=str(ss)),audit=dict(path=str(audit),sha256=sha(audit),snapshot=str(aa)),
  manifest=descriptor(manifest),generator=descriptor(generator),provider_evidence=[dict(path=p,sha256=h) for p,h in evidence.items()],parent_summaries=summaries,
  reused_modules=[selected[m] for m in closure],exact_project_import_closure=True,project_module_count=22,external_project_boundaries=[],
  toolchain_providers=tools,actual_first_providers=actual,actual_direct_tool_imports=sorted(tool_names),before=before,commands=[],fresh_modules=[],LEAN_PATH=str(cache),
  dependency_build=False,downloads=False,per_command_timeout_seconds=TIMEOUT,shared_wall_seconds=TIMEOUT,
  limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),expected_named_axiom_probes=2,expected_callers=callers)
 def save():(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
 def post():
  record['after']={str(p):sha(p) for p in inputs};need(record['after']==before,'Input/provider changed.')
  for m in closure:
   need(first(m).resolve()==Path(selected[m]['object']).resolve() and sha(first(m))==selected[m]['object_sha256'],'First provider changed.')
  for q in tools:need(first(q['module']).resolve()==Path(q['object']).resolve() and sha(first(q['module']))==q['object_sha256'],'Tool provider changed.')
  record['all_input_provider_postchecks']=True
 save()
 try:
  if args.prepare_only:post();save();return record
  deadline=time.monotonic()+TIMEOUT
  def run(label,path,obj=None):
   cmd=[str(compiler),'-j1','-M4096','--root='+str(snap)]
   if obj is not None:cmd+=['-o',str(obj)]
   cmd+=[str(path)];began=time.monotonic();remaining=deadline-began
   need(remaining>0,'Shared proof wall budget exhausted.')
   timed_out=False
   try:
    result=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True,timeout=remaining)
    output,code=result.stdout+result.stderr,result.returncode
   except subprocess.TimeoutExpired as ex:
    decode=lambda x:x.decode(errors='replace') if isinstance(x,bytes) else x or ''
    output,code=decode(ex.stdout)+decode(ex.stderr)+'\nTIMEOUT\n',None;timed_out=True
   log=work/(label+'.log');log.write_text(output)
   record['commands'].append(dict(label=label,command=cmd,cwd=str(snap),seconds=time.monotonic()-began,exit_code=code,
                                  timed_out=timed_out,log=str(log),output=output));save()
   need(code==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,label+' failed; inspect '+str(log))
   return output
  obj=cache/Path(module.replace('.','/')).with_suffix('.olean')
  run('source',ss,obj);need(obj.is_file() and not obj.is_symlink(),'Fresh source object missing.')
  fresh=dict(module=module,path=str(obj),sha256=sha(obj),source_sha256=sha(source))
  record.update(source_object_recorded_before_audit=True,source_pass_object=dict(fresh,source_command_index=0),fresh_modules=[fresh])
  need(first(module).resolve()==obj.resolve(),'Fresh module not first.')
  record['fresh_first_provider_before_audit']=dict(module=module,actual_first=str(first(module)),resolved=str(obj.resolve()),sha256=sha(obj));save()
  output=run('audit',aa)
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",output,re.S)
  need([n for n,_ in reports]==[prefix+n for n in PROBES],'Missing/reordered audit reports.')
  axioms=[dict(name=n,axioms=[x.strip() for x in block.split(',') if x.strip()]) for n,block in reports]
  record['actual_axiom_sets']=axioms;save()
  need(all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in axioms),'Unexpected axioms.')
  post();need(sha(obj)==fresh['sha256'] and first(module).resolve()==obj.resolve(),'Fresh object changed during audit.')
  record.update(status='PASS',all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=2,callers=callers,only_standard_axioms=True,
                warnings={q['label']:q['output'].count('warning:') for q in record['commands']})
 except Exception as ex:
  record.update(status='FAIL',error=str(ex))
  try:post()
  except Exception as pe:record['postcheck_error']=str(pe)
  save();raise
 save();return record

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--repo',type=Path,required=True)
 ap.add_argument('--manifest',type=Path,default=HERE/'pilot-plan.json')
 ap.add_argument('--generator',type=Path,default=HERE/'prepare_pilots.py')
 ap.add_argument('--site-evidence',type=Path,default=Path(PARENTS['site'][0]))
 ap.add_argument('--program-evidence',type=Path)
 choose=ap.add_mutually_exclusive_group();choose.add_argument('--leaf',type=int,action='append',choices=ORDER);choose.add_argument('--all',action='store_true')
 ap.add_argument('--output',type=Path,required=True);ap.add_argument('--prepare-only',action='store_true');args=ap.parse_args()
 if not __debug__:ap.error('Python assertions must remain enabled.')
 if args.program_evidence is None:args.program_evidence=args.repo/PARENTS['program'][0]
 repo=args.repo.resolve();work=args.output.resolve()
 need(not work.is_relative_to(repo) and (not work.exists() or not any(work.iterdir())),'Use a new/empty external output.')
 need(sha(args.manifest)==MANIFEST_SHA and sha(args.generator)==GENERATOR_SHA,'Changed manifest or source emitter.')
 plan=json.loads(args.manifest.read_text());units={u['site_index']:u for u in plan['pilots']}
 need(len(units)==len(plan['pilots'])==7 and set(units)==set(ORDER) and plan['pilot_guard_cases']==9,'Exact pilot set differs.')
 need(plan['measurement_policy']==dict(independent_unit_timeout_seconds=120,source_and_audit_share_budget=True,threads=1,memory_mib=4096,proof_limits='default',site_fuel=4000,header_margin=64),'Measurement policy differs.')
 keys=ORDER if args.all else args.leaf or [ORDER[0]];need(len(set(keys))==len(keys),'Duplicate leaf selection.')
 work.mkdir(parents=True,exist_ok=True)
 batch=dict(status='RUNNING',prepare_only=args.prepare_only,guard=descriptor(Path(__file__).resolve()),manifest=descriptor(args.manifest.resolve()),
            selected_leaf_indices=keys,frozen_full_order=ORDER,completed_units=[],failed_leaf=None,serial=True,shared_wall_seconds_per_unit=120,
            compiler_version_query_performed=False,dependency_build=False,downloads=False,scope='Only selected measured leaves; no all-sites or endpoint claim.')
 def save():(work/'batch.json').write_text(json.dumps(batch,indent=2)+'\n')
 save()
 try:
  for i in keys:
   output=work/f'case{i:04d}';result=run_unit(args,plan,units[i],output)
   need(result['status']==('PREPARED_NOT_BUILT' if args.prepare_only else 'PASS'),'Incomplete unit cannot be accepted.')
   batch['completed_units'].append(dict(leaf_index=i,status=result['status'],record=descriptor(output/'verification.json')));save()
  batch['status']='PREPARED_NOT_BUILT' if args.prepare_only else 'PASS_SELECTED_PILOTS'
 except Exception as ex:
  record=work/f'case{i:04d}'/'verification.json'
  batch.update(status='FAIL',failed_leaf=i,error=str(ex),failed_record=descriptor(record) if record.is_file() else None,
               failure_stage='RECORDED_UNIT_FAILURE' if record.is_file() else 'PREPARATION_REJECTED_BEFORE_COMPILER')
  save();raise
 save();print(work/'batch.json')

if __name__=='__main__':main()
