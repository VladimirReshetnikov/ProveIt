from pathlib import Path
import ast,difflib,hashlib
B=Path('/tmp/zfc-routing245-lean/coverage-production');old=Path('/tmp/zfc-routing245-lean/coverage-subtree-pilots/check-subtrees.py').read_text();s=old
x=s.index('"""');y=s.index('"""',x+3)+3
s=s[:x]+'''"""Serial exact245 production coverage, one shared120s source/audit budget per unit.
Pins the complete100-unit source manifest. Direct imports select exact already
successful parents; three measured pilot modules are reused without proof replay.
Every unit saves a PREPARED_NOT_BUILT receipt before source execution, then fresh
object before audit. Stop on first failure; resume only in a new output directory
with explicit previous batch records. No dependency builds, downloads, compiler
version query, automatic repair, enlarged proof limits, or proof parallelism.
"""'''+s[y:]
s=s.replace("MANIFEST_SHA='c861f4b83dd94980edaece32b92c74f5a7e876d3c920ece6a616e7fd8d6cf60b'", "MANIFEST_SHA='acc22343a70173e143ccf7cef76c9c7dfa7632b2526d3ca5735cb7d582062f24'")
s=s.replace("GENERATOR_SHA='146176f7f6cc8c53d673e8d3a544e3af865b5cfbe2442e7dd871a293a751fca1'", "GENERATOR_SHA='c428e2878845b0af2fd87c479b7fbb0d7beb4a35b4dab311fecc193175a34fb8'")
a=s.index('ORDER=');z=s.index('TIMEOUT=120',a)
s=s[:a]+"BASE_IMPORTS=['BusyBeaver.ZFC.ProgramRouting245','BusyBeaver.ZFC.SiteCoverage','BusyBeaver.ZFC.SiteRouting245']\n"+s[z:]
s=s.replace('def run_unit(args,plan,unit,work):','def run_unit(args,plan,unit,index,work,available):')
a=s.index(' module=unit');z=s.index(' for entry in plan[',a)
s=s[:a]+''' module=unit['module'];prefix='SetTheory.BusyBeaver.ZFC.SitesRouting245.'
 probes=unit['probe_names'];callers=unit['callers'];direct=unit['imports']
 need(not work.exists() and not work.is_relative_to(repo),'Use a fresh external unit output.')
 need(unit['probes']==len(probes)==callers and direct[:3]==BASE_IMPORTS,'Unit descriptor differs.')
 source=(manifest.parent/unit['source']).resolve();audit=(manifest.parent/unit['audit']).resolve()
 boundary=HERE.parent/'coverage-subtree-pilots/boundary-plan.json'
 need(sha(boundary)==BOUNDARY_SHA,'Changed base provider inventory.')
 inputs=[Path(__file__).resolve(),manifest,generator,boundary]
'''+s[z:]
a=s.index(' # Revalidate every');z=s.index(' selected={}',a)
s=s[:a]+''' # All200 generated source/audit files remain bound, even for a selected range.
 for entry in plan['units']:
  for role in ('source','audit'):
   p=(manifest.parent/entry[role]).resolve();need(sha(p)==entry[role+'_sha256'],'Changed generated '+str(p));inputs.append(p)
 need(sha(manifest)==MANIFEST_SHA and sha(generator)==GENERATOR_SHA,'Changed generation manifest/emitter.')
 st,at=source.read_text(),audit.read_text()
 need(imports(source)==direct and imports(audit)==[module],'Generated imports differ.')
 need(re.findall(r'^theorem (\\w+)',st,re.M)==probes,'Generated theorem census differs.')
 need(re.findall(r'^#print axioms (\\S+)$',at,re.M)==[prefix+n for n in probes] and
      len(re.findall(r'^example\\b',at,re.M))==callers,'Generated audit census differs.')
 for text in (st,at):
  need(not re.search(r'\\b(sorry|admit|native_decide)\\b|^axiom\\s',text,re.M),'Forbidden proof shortcut.')
  need(not re.search(r'set_option\\s+(maxHeartbeats|maxRecDepth)',text),'Keep default proof limits.')
 parents=[]
 for label,(_,pin,parent_module,parent_probes,parent_callers) in PARENTS.items():
  parents.append((label,getattr(args,label+'_evidence').resolve(),pin,parent_module,parent_probes,parent_callers))
 for m in direct[3:]:
  need(m in available,'Direct parent has no actual PASS record: '+m)
  ref=available[m];expected=unit_descriptor(plan,m)
  parents.append((m,Path(ref['path']).resolve(),ref['sha256'],m,expected['probes'],expected['callers']))
'''+s[z:]
s=s.replace(" for label,(_,pin,parent_module,probes,parent_callers) in PARENTS.items():\n  e=getattr(args,label+'_evidence').resolve();need(sha(e)==pin,'Changed '+label+' parent record')", " for label,e,pin,parent_module,parent_probes,parent_callers in parents:\n  need(sha(e)==pin,'Changed '+label+' parent record')")
s=s.replace("(parent['named_axiom_probes'],parent['callers'])==(probes,parent_callers)","(parent['named_axiom_probes'],parent['callers'])==(parent_probes,parent_callers)")
# Any dynamic fresh source must be exactly the frozen generated/pilot source.
needle="  s=Path(parent['source']['path']).resolve()\n  need(q['source_sha256']"
s=s.replace(needle,"  s=Path(parent['source']['path']).resolve()\n  if parent_module not in BASE_IMPORTS:\n   expected=unit_descriptor(plan,parent_module)\n   need(parent['source']['sha256']==expected['source_sha256'] and parent['audit']['sha256']==expected['audit_sha256'],'Parent does not match frozen generated source/audit.')\n  need(q['source_sha256']")
s=s.replace(" need(set(expected)==set(selected),'Provider set differs from frozen boundary inventory.')\n for m,q in selected.items():", " need(set(expected)<=set(selected),'Base provider missing from frozen boundary inventory.')\n for m in expected:\n  q=selected[m]")
s=s.replace(' for m in DIRECT:visit(m)', ' for m in direct:visit(m)')
s=s.replace("need(set(closure)==set(selected) and len(closure)==23,'Exact23-project closure differs.')", "need(set(closure)==set(selected) and len(closure)>=23,'Exact direct-import project closure differs.')")
s=s.replace("record=dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING'", "record=dict(status='PREPARED_NOT_BUILT'")
s=s.replace("  cut_index=i,path_bits=path,leaf_interval=[lo,hi],leaf_count=leaves,subtree_height=height,guard_cases=guards,site_fuel=4000,margin=64,", "  unit_index=index,module=module,unit_kind=unit['kind'],cuts=unit.get('cuts',[]),guard_cases=unit.get('guards'),site_fuel=4000,margin=64,")
s=s.replace("prepare_only=args.prepare_only,scope=__doc__", "prepare_only=True,scope=__doc__")
s=s.replace('project_module_count=23','project_module_count=len(closure)').replace('expected_named_axiom_probes=1','expected_named_axiom_probes=len(probes)')
s=s.replace("  if args.prepare_only:post();save();return record\n  deadline=", "  post();save()\n  preparation=work/'preparation.json';preparation.write_text(json.dumps(record,indent=2)+'\\n')\n  if args.prepare_only:return record\n  record.update(status='RUNNING',prepare_only=False,preparation=descriptor(preparation));save()\n  deadline=")
s=s.replace('[prefix+n for n in PROBES]','[prefix+n for n in probes]').replace('named_axiom_probes=1,callers=callers','named_axiom_probes=len(probes),callers=callers')
s=s.replace(' except Exception as ex:\n  record.update', ' except BaseException as ex:\n  record.update')
a=s.index('\ndef main():');s=s[:a]+'''
def unit_descriptor(plan,module):
 for u in plan['units']:
  if u['module']==module:return u
 for u in plan['reused_units']:
  if u['full_module']==module:
   return dict(module=module,source_sha256=u['source']['sha256'],audit_sha256=u['audit']['sha256'],
               probes=u['probes'],callers=u['callers'],probe_names=['checked'],pilot=True)
 raise RuntimeError('Module absent from frozen complete plan: '+module)

def successful_receipt(plan,module,ref):
 """Recheck an actual prior/pilot receipt; preparation never becomes a provider."""
 p=Path(ref['path']).resolve();need(sha(p)==ref['sha256'],'Changed actual record '+str(p))
 d=json.loads(p.read_text());u=unit_descriptor(plan,module)
 need(d['status']=='PASS' and d['prepare_only'] is False and d['before']==d['after'] and
      all(d[k] for k in ('only_standard_axioms','source_object_recorded_before_audit',
                        'all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit')),'Incomplete actual record.')
 need((d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers']),'Prior audit census differs.')
 for p0,h in d['before'].items():need(sha(p0)==h,'Stale prior input '+p0)
 need([c['label']for c in d['commands']]==['source','audit'],'Wrong prior command order.')
 for c in d['commands']:
  need(c['exit_code']==0 and not c.get('timed_out',False) and c['command'][1:3]==['-j1','-M4096'],'Failed prior proof command.')
  need((p.parent/(c['label']+'.log')).read_text()==c['output'],'Prior raw proof log differs.')
 for role in ('source','audit'):
  q=d[role];need(sha(q['path'])==sha(q['snapshot'])==q['sha256']==u[role+'_sha256'],'Prior source/audit differs.')
 actuals={q['module']:q for q in d['actual_first_providers']}
 need(len(actuals)==len(d['actual_first_providers'])==len(d['reused_modules']),'Prior provider census differs.')
 for q in d['reused_modules']:
  need(all(sha(q[k])==q[k+'_sha256']==d['before'][q[k]]==d['after'][q[k]] for k in ('source','object')),'Prior reused provider differs.')
  actual=actuals[q['module']]
  need(first_path(actual)==Path(q['object']).resolve() and actual['sha256']==q['object_sha256'],'Prior first provider differs.')
 fs=d['fresh_modules'];need(len(fs)==1 and fs[0]['module']==module,'Wrong prior fresh module.')
 f=fs[0];need(all(f[k]==d['source_pass_object'][k] for k in ('module','path','sha256','source_sha256')),'Prior object was not captured before audit.')
 actual=d['fresh_first_provider_before_audit']
 need(sha(f['path'])==f['sha256']==actual['sha256'] and first_path(actual)==Path(f['path']).resolve() and
      actual['module']==module and f['source_sha256']==u['source_sha256'],'Prior fresh object differs.')
 prefix='SetTheory.BusyBeaver.ZFC.'+module.rsplit('.',1)[1]+'.' if u.get('pilot') else 'SetTheory.BusyBeaver.ZFC.SitesRouting245.'
 reports=re.findall(r"'([^']+)'\\s+(?:depends on axioms:\\s*\\[([^\\]]*)\\]|does not depend on any axioms)",d['commands'][1]['output'],re.S)
 parsed=[dict(name=n,axioms=[x.strip() for x in block.split(',') if x.strip()]) for n,block in reports]
 need(parsed==d['actual_axiom_sets'] and [q['name'] for q in parsed]==[prefix+n for n in u['probe_names']] and
      all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in parsed),'Prior raw axiom reports differ.')
 return d

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--repo',type=Path,required=True)
 ap.add_argument('--manifest',type=Path,default=HERE/'sources/generation.json')
 ap.add_argument('--generator',type=Path,default=HERE/'generate_sites_routing245.py')
 ap.add_argument('--site-evidence',type=Path,default=Path(PARENTS['site'][0]))
 ap.add_argument('--program-evidence',type=Path);ap.add_argument('--coverage-evidence',type=Path)
 ap.add_argument('--start',type=int,default=0);ap.add_argument('--count',type=int,default=1)
 ap.add_argument('--prior-batch',type=Path,action='append',default=[])
 ap.add_argument('--output',type=Path,required=True);ap.add_argument('--prepare-only',action='store_true');args=ap.parse_args()
 if not __debug__:ap.error('Python assertions must remain enabled.')
 if args.program_evidence is None:args.program_evidence=args.repo/PARENTS['program'][0]
 if args.coverage_evidence is None:args.coverage_evidence=args.repo/COVERAGE_EVIDENCE[0]
 repo=args.repo.resolve();work=args.output.resolve()
 need(not work.is_relative_to(repo) and(not work.exists()or not any(work.iterdir())),'Use a fresh external batch output.')
 need(sha(args.manifest)==MANIFEST_SHA and sha(args.generator)==GENERATOR_SHA,'Changed exact production manifest/emitter.')
 plan=json.loads(args.manifest.read_text());units=plan['units'];modules=[u['module'] for u in units]
 need(len(modules)==len(set(modules))==100 and plan['chunks']==236 and plan['joins']==235 and
      plan['leaves']==6460 and plan['guard_cases']==8391 and plan['decoder_depth']==51 and
      (plan['max_guards_per_cut'],plan['max_cuts_per_module'],plan['max_batch_guards'],plan['joins_per_module'])==(64,4,128,16) and
      (plan['generated_probes'],plan['generated_callers'],plan['complete_probes'],plan['complete_callers'])==(471,471,474,477),'Wrong complete production plan.')
 need(args.start>=0 and args.count>0 and args.start+args.count<=100,'Invalid selected range.')
 keys=list(range(args.start,args.start+args.count));available={};prior_refs=[]
 for u in plan['reused_units']:
  ref=u['record'];successful_receipt(plan,u['full_module'],ref);available[u['full_module']]=ref
 need(len(available)==3,'Exactly three measured pilot modules required.')
 for file in args.prior_batch:
  file=file.resolve();d=json.loads(file.read_text());prior_refs.append(descriptor(file))
  need(d['manifest']['sha256']==MANIFEST_SHA and d['prepare_only'] is False,'Wrong or prepared prior batch.')
  for row in d['completed_units']:
   i=row['unit_index'];need(0<=i<100 and modules[i]==row['module'] and row['status']=='PASS','Invalid prior unit.')
   ref=row['record'];successful_receipt(plan,row['module'],ref)
   if row['module'] in available:need(available[row['module']]['sha256']==ref['sha256'],'Conflicting successful records for one module.')
   else:available[row['module']]=ref
 need(all(modules[i] not in available for i in keys),'Do not replay already successful selected modules.')
 work.mkdir(parents=True,exist_ok=True)
 batch=dict(status='RUNNING',prepare_only=args.prepare_only,guard=descriptor(Path(__file__).resolve()),manifest=descriptor(args.manifest.resolve()),
            selected_unit_indices=keys,prior_batches=prior_refs,pilot_reuse=[u['record'] for u in plan['reused_units']],
            completed_units=[],failed_unit=None,serial=True,shared_wall_seconds_per_unit=120,
            compiler_version_query_performed=False,dependency_build=False,downloads=False,
            scope='Exact selected closed coverage units. A complete coverage claim requires all100 actual units plus three actual reused pilots; no bootstrap or PA claim.')
 def save():
  tmp=work/'batch.json.tmp';tmp.write_text(json.dumps(batch,indent=2)+'\\n');tmp.replace(work/'batch.json')
 save()
 try:
  for i in keys:
   for p in prior_refs:need(sha(p['path'])==p['sha256'],'Prior batch history changed.')
   batch['active_unit']=dict(index=i,module=modules[i]);save()
   output=work/f'unit{i:03d}';result=run_unit(args,plan,units[i],i,output,available)
   need(result['status']==('PREPARED_NOT_BUILT' if args.prepare_only else 'PASS'),'Incomplete unit cannot be accepted.')
   ref=descriptor(output/'verification.json')
   if not args.prepare_only:
    successful_receipt(plan,modules[i],ref);available[modules[i]]=ref
   batch['completed_units'].append(dict(unit_index=i,module=modules[i],status=result['status'],record=ref,
                                       preparation=descriptor(output/'preparation.json')));save()
  batch.update(status='PREPARED_NOT_BUILT' if args.prepare_only else 'PASS_SELECTED_UNITS',active_unit=None)
  if not args.prepare_only and all(m in available for m in modules):
   for m in modules:successful_receipt(plan,m,available[m])
   batch.update(status='PASS_COMPLETE_COVERAGE',complete_generated_units=100,reused_pilot_units=3,
                complete_probes=474,complete_callers=477,final_record=available['BusyBeaver.ZFC.SitesRouting245'])
 except BaseException as ex:
  record=work/f'unit{i:03d}'/'verification.json'
  batch.update(status='FAIL',failed_unit=i,error=f'{type(ex).__name__}: {ex}',failed_record=descriptor(record) if record.is_file() else None,
               failure_stage='RECORDED_UNIT_FAILURE' if record.is_file() else 'PREPARATION_REJECTED_BEFORE_COMPILER')
  save();raise
 save();print(work/'batch.json')

if __name__=='__main__':main()
'''
ast.parse(s)
(B/'check-production.py').write_text(s)
(B/'guard-from-subtrees.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='reviewed-subtrees/check-subtrees.py',tofile='production/check-production.py')))
print(len(s.splitlines()),hashlib.sha256(s.encode()).hexdigest())
