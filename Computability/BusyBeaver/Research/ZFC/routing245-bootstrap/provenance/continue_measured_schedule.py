#!/usr/bin/env python3
"""Root-invoked serial measured bootstrap schedule, groups03–09 only.
Each proof guard retains its own shared120s/-j1/-M4096/default proof limits.
Generated literal data are untrusted until actual source+audit PASS. This
coordinator preserves every command/output and stops at the first failure.
No dependency build, download, compiler version query or automatic proof repair.
"""
from pathlib import Path
import argparse,ast,hashlib,json,os,re,signal,subprocess,sys,time
BASE=Path('/tmp/zfc-routing245-lean')
PLAN=BASE/'bootstrap-plan'
PINS={
 'measured-schedule-v1.json':'f2911dd49269cef9602bcaec7804f56aaf5b233def056998a467fa4b4f18f526',
 'generate.py':'610fa3ae21f146dadf8f2346702b99a54da12cf6271a4427a74e4456bdf03016',
 'prepare_continuation_guard.py':'25397147110e8417e823a9027085ce72a6dd7ff3c77d514afb7f10484cabdcf2'}
TEMPLATE=BASE/'bootstrap-first/check.py'
TEMPLATE_SHA='8f8b3b6c734408b5757d62004cdd93f5cd3b7f87614fca27292b1e93554c3714'
TABLE_REL='Computability/BusyBeaver/Research/ZFC/candidate-routing245/zfc_routing245.tm'
TABLE_SHA='17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13'
GROUP03={'BootRouting245Chunk003.lean':'8985ff0c38ea3351648304bcddd4825a9c722d3f5f19cf39095c864b30c5d80b',
 'Audit.lean':'1032643f65d07dfd2a1a9645ed23c6d268cbb959118c2d5d751ec2f49bb49516',
 'data.json':'e9230622a38b9b53cea697ff3230020f9b6e2e872a12aa996c2b7da02de2ec42',
 'source-inventory.json':'8ff1e704eb25b8381e1a3c32016b0b242278aa817f447d7d04b0ccd31b8598c0',
 'check.py':'a7f368e2d6f1ef22b3c95a30f1c3e566f4ccfb4cebd41d2de5b24d9071699daa'}

def need(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p):return dict(path=str(p),sha256=sha(p))
def load(p):return json.loads(Path(p).read_text())
def pin(p,h):need(sha(p)==h,'Changed input '+str(p))
def norm(s):return re.sub(r'\s+','',s)
def write(p,d):
 t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(d,indent=2)+'\n');t.replace(p)
def module(i):return f'BusyBeaver.ZFC.BootRouting245Chunk{i:03d}'
def unit(i):return BASE/'bootstrap-chunks'/f'group{i:02d}'
def config(text,name):
 pat=r'def '+re.escape(name)+r' : ZipConfig 245 :=\s*\{ state := some ⟨(\d+), by decide⟩, head := (-?\d+),\s*left := (.*?),\s*right := (.*?) \}'
 m=re.search(pat,text,re.S);need(m is not None,'Missing exact finite configuration '+name)
 def bits(s):
  need(re.fullmatch(r'\s*\[(?:\s*(?:true|false)\s*(?:,\s*(?:true|false)\s*)*)?\](?:\s*\+\+\s*\[(?:\s*(?:true|false)\s*(?:,\s*(?:true|false)\s*)*)?\])*\s*',s) is not None,'Nonliteral tape expression')
  return [int(x=='true')for x in re.findall(r'\b(?:true|false)\b',s)]
 return dict(state=int(m[1]),head=int(m[2]),left=bits(m[3]),right=bits(m[4])),m

def record(p,i,prepared=False):
 r=load(p);need(r['status']==('PREPARED_NOT_BUILT'if prepared else'PASS') and r['prepare_only'] is prepared,'Incomplete actual record '+str(p))
 for f,h in r['before'].items():pin(f,h)
 for role in ['source','audit']:
  q=r[role];pin(q['path'],q['sha256']);pin(q['snapshot'],q['sha256'])
 need(r['exact_project_import_closure'] and r['project_module_count']==4+i and len(r['reused_modules'])==4+i,'Wrong selected project closure')
 for q in r['reused_modules']:
  pin(q['source'],q['source_sha256']);pin(q['object'],q['object_sha256'])
 for q in r['actual_first_providers']:
  pin(q['actual_first'],q['sha256']);need(Path(q['actual_first']).resolve()==Path(q['resolved']).resolve(),'Wrong first provider')
 for q in r['toolchain_providers']:pin(q['actual_first'],q['object_sha256'])
 need(r['shared_wall_seconds']==120 and r['per_command_timeout_seconds']==120 and not r['dependency_build'] and not r['downloads'],'Changed resource/build policy')
 if prepared:
  need(r['commands']==[] and r['fresh_modules']==[],'Preparation performed proof work')
  return r
 inv=load(unit(i)/'source-inventory.json')
 need(r['before']==r['after'] and all(r[k]for k in ['only_standard_axioms','source_object_recorded_before_audit','all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit']),'Incomplete proof postchecks')
 need((r['named_axiom_probes'],r['callers'])==(len(inv['probes']),inv['callers']),'Wrong actual audit census')
 need([q['label']for q in r['commands']]==['source','audit'],'Wrong actual commands')
 for q in r['commands']:
  need(q['exit_code']==0 and not q.get('timed_out',False)and q['command'][1:3]==['-j1','-M4096'],'Failed or changed proof command')
  need((p.parent/(q['label']+'.log')).read_text()==q['output'],'Raw output differs')
 need(r['fresh_modules']==[r['source_pass_object']] and r['fresh_modules'][0]['module']==module(i),'Wrong fresh module')
 f=r['fresh_modules'][0];pin(f['path'],f['sha256'])
 need(f['source_sha256']==r['source']['sha256']==inv['source']['sha256'] and r['audit']['sha256']==inv['audit']['sha256'],'Wrong actual source binding')
 need(r['fresh_first_provider_before_audit']['sha256']==f['sha256'],'Wrong pre-audit fresh object')
 reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",r['commands'][1]['output'])
 parsed=[dict(name=n,axioms=a.split(', ')if a else[])for n,a in reports]
 need(parsed==r['actual_axiom_sets'] and [q['name']for q in parsed]==inv['probes'],'Wrong raw axiom reports')
 need(all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'}for q in parsed),'Nonstandard axiom')
 return r

def inspect(row,previous_record,repo):
 i=row['group'];U=unit(i);inv=load(U/'source-inventory.json');data=load(U/'data.json');ns=module(i).rsplit('.',1)[1];pn=module(i-1).rsplit('.',1)[1]
 need((inv['unit_index'],inv['module'],inv['start'],inv['endpoint'])==(i,module(i),row['start'],row['endpoint']),'Wrong generated unit interval')
 segments=[];at=row['start']
 for d in row['depths']:segments.append(dict(start=at,end=at+2**d,depth=d));at+=2**d
 need(inv['segments']==data['segments']==segments and at==row['endpoint'],'Changed block schedule')
 need(inv['imports']==[module(i-1)] and inv['parents']==[dict(**desc(previous_record),module=module(i-1))],'Wrong predecessor import/evidence')
 need(inv['metadata_inputs']==[desc(unit(i-1)/'source-inventory.json')],'Wrong predecessor inventory')
 for role in ['source','audit','data','generator','canonical']:
  q=inv[role];pin(q['path'],q['sha256'])
 need(Path(inv['source']['path'])==U/(ns+'.lean') and Path(inv['audit']['path'])==U/'Audit.lean' and Path(inv['data']['path'])==U/'data.json','Unexpected payload paths')
 need(inv['generator']==desc(PLAN/'generate.py') and inv['canonical']==desc(repo/TABLE_REL),'Wrong generator/table')
 need(data['status']=='UNTRUSTED_GENERATED_INPUTS' and data['proof_execution']is False and data['table']==inv['canonical'],'Generated data scope mismatch')
 need(set(data['checkpoints'])=={str(row['start'])}|{str(q['end'])for q in segments},'Wrong checkpoint set')
 source=Path(inv['source']['path']).read_text();audit=Path(inv['audit']['path']).read_text();stripped=re.sub(r'/\-!.*?\-/','',source,flags=re.S)
 expected=f'import {module(i-1)}\nnamespace SetTheory.BusyBeaver.ZFC.{ns}\nopen FiniteZipper FastTableRouting245\n';probes=[];examples=[]
 prev_z=pn+'.checkpoint'+str(row['start']);prev_h=pn+'.reached'+str(row['start'])
 prev_inv=load(unit(i-1)/'source-inventory.json');old_conf,_=config(Path(prev_inv['source']['path']).read_text(),'checkpoint'+str(row['start']))
 need(all(data['checkpoints'][str(row['start'])][k]==v for k,v in old_conf.items()),'Data start differs from checked predecessor')
 for q in segments:
  end=q['end'];z=f'checkpoint{end}';b=f'block{end}';h=f'reached{end}';d=q['depth'];v,m=config(source,z);actual=data['checkpoints'][str(end)]
  need(all(actual[k]==v[k]for k in v),'Literal checkpoint differs from generated data')
  need(0<=v['state']<245,'Unexpected halted checkpoint')
  support=sorted([v['head']-j-1 for j,x in enumerate(v['left'])if x]+[v['head']+j for j,x in enumerate(v['right'])if x]);need(support==actual['ones'],'Incomplete literal support')
  stripped=stripped.replace(m[0],f'CONFIG_{end}',1)
  expected+=f'CONFIG_{end}\ntheorem {b} : zipBlock fastMachine {d} {prev_z} = {z} := by decide +kernel\ntheorem {h} : ZipRep (machineRouting245.run {end}) {z} := BootRouting245First.advance_checkpoint {q["start"]} {d} {prev_h} {b}\n'
  probes.extend([b,h]);examples.extend([f'example : zipBlock fastMachine {d} {prev_z} = {z} := {b}',f'example : ZipRep (machineRouting245.run {end}) {z} := {h}']);prev_z=z;prev_h=h
 if row['endpoint']==407915:
  expected+='theorem bootstrap407915 : ZipRep (machineRouting245.run 407915) checkpoint407915 := reached407915\ntheorem bootstrap_active_through : ∀ elapsed, elapsed ≤ 407915 → (machineRouting245.run elapsed).state ≠ none := by apply active_through_of_endpoint rw [bootstrap407915.1] decide\n'
  probes+=['bootstrap407915','bootstrap_active_through'];examples+=['example : ZipRep (machineRouting245.run 407915) checkpoint407915 := bootstrap407915','example (t : Nat) (h : t ≤ 407915) : (machineRouting245.run t).state ≠ none := bootstrap_active_through t h']
  v=data['checkpoints']['407915'];file=[0,0,0,3,0,0,3,0,0]+[1]*167
  need(v['state']==88 and v['head']==-5 and v['left']==[1]+[0]*10 and v['right']==[0]*181+[1]+[b for n in file for b in [0]+[1]*(n+1)] and len(v['ones'])==351,'Exact final whole frame differs')
 expected+=f'end SetTheory.BusyBeaver.ZFC.{ns}\n';need(norm(stripped)==norm(expected),'Source proof skeleton differs')
 end=row['endpoint'];examples += [f'example : (machineRouting245.run {end}).state = {prev_z}.state := {prev_h}.1',f'example : (machineRouting245.run {end}).head = {prev_z}.head := {prev_h}.2.1',f'example (p : Int) : Tape.read (machineRouting245.run {end}).tape p = frameRead {prev_z} p := read_eq_frameRead {prev_h} p']
 names=['SetTheory.BusyBeaver.ZFC.'+ns+'.'+n for n in probes]
 expected_a=f'import {module(i)}\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen FiniteZipper FastTableRouting245 {ns}\n'+'\n'.join('#print axioms '+n for n in names)+'\n'+'\n'.join(examples)
 need(norm(audit)==norm(expected_a) and inv['probes']==names and inv['callers']==len(examples)==row['callers'] and len(names)==row['probes'],'Audit contract differs')
 guard=(U/'check.py').read_text();binding=load(U/'guard-binding.json');need(binding['guard']==desc(U/'check.py') and binding['inventory']==desc(U/'source-inventory.json') and binding['parent']==desc(previous_record),'Guard binding differs')
 need(binding['adaptor']==desc(PLAN/'prepare_continuation_guard.py') and binding['template']==desc(TEMPLATE),'Wrong guard emitter/template')
 need(guard.split('def save():',1)[1]==TEMPLATE.read_text().split('def save():',1)[1],'Changed execution tail')
 values={}
 for node in ast.parse(guard).body:
  if isinstance(node,ast.Assign)and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
   try:values[node.targets[0].id]=ast.literal_eval(node.value)
   except(ValueError,TypeError):pass
 prev=load(previous_record)
 wanted=dict(MODULE=module(i),PREFIX='SetTheory.BusyBeaver.ZFC.'+ns+'.',SOURCE_SHA=inv['source']['sha256'],AUDIT_SHA=inv['audit']['sha256'],DATA_SHA=inv['data']['sha256'],INVENTORY_SHA=sha(U/'source-inventory.json'),GENERATOR_SHA=PINS['generate.py'],TABLE_SHA=TABLE_SHA,PROBES=probes,CALLERS=len(examples),TIMEOUT=120,PARENTS={'previous':(str(previous_record),sha(previous_record),module(i-1),prev['named_axiom_probes'],prev['callers'])})
 need(all(values[k]==v for k,v in wanted.items()),'Guard constants differ')
 return dict(status='STATIC_PATTERN_AND_LITERAL_BINDINGS_CHECKED',module=module(i),start=row['start'],endpoint=end,source=inv['source'],audit=inv['audit'],data=inv['data'],inventory=desc(U/'source-inventory.json'),guard=desc(U/'check.py'),probes=len(names),callers=len(examples),checkpoint_simulation_by_this_check=False)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 need(__debug__,'Assertions must remain enabled');repo=args.repo.resolve();out=args.output.resolve()
 need(not out.is_relative_to(repo)and(not out.exists()or not any(out.iterdir())),'Use new empty external coordination output')
 for f,h in PINS.items():pin(PLAN/f,h)
 pin(TEMPLATE,TEMPLATE_SHA);pin(repo/TABLE_REL,TABLE_SHA)
 schedule=load(PLAN/'measured-schedule-v1.json');rows=schedule['groups'][2:];need([r['group']for r in rows]==list(range(3,10)),'Wrong remaining schedule')
 for f,h in GROUP03.items():pin(unit(3)/f,h)
 for i in range(4,10):need(not unit(i).exists(),'Future unit already exists: preserve it and request a successor coordinator')
 for i in range(3,10):
  need(not(unit(i)/'prepared1').exists()and not(unit(i)/'run1').exists(),'Do not overwrite unit attempt')
 previous=unit(2)/'run1/verification.json';pin(previous,schedule['groups'][1]['record_sha256']);record(previous,2)
 out.mkdir(parents=True,exist_ok=True)
 progress=dict(status='RUNNING',scope='Remaining actual routing245 blank bootstrap only; runtime frame, coverage, endpoint and PA remain separate.',coordinator=desc(Path(__file__).resolve()),schedule=desc(PLAN/'measured-schedule-v1.json'),selected_groups=list(range(3,10)),completed=[],commands=[],active=None,serial=True,proof_limits='default',shared_source_audit_seconds=120)
 def save():write(out/'coordination.json',progress)
 save()
 def launch(label,cmd,timeout):
  log=out/(label+'.log');c=dict(label=label,command=[str(x)for x in cmd],status='STARTING',output_path=str(log),timeout_seconds=timeout);progress['commands'].append(c);save();start=time.monotonic()
  with log.open('wb')as f:
   proc=subprocess.Popen(c['command'],stdout=f,stderr=subprocess.STDOUT,start_new_session=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
   c.update(status='RUNNING',pid=proc.pid);save()
   try:code=proc.wait(timeout=timeout)
   except subprocess.TimeoutExpired:
    os.killpg(proc.pid,signal.SIGKILL);code=proc.wait();c['timed_out']=True
   except BaseException as ex:
    if proc.poll() is None:os.killpg(proc.pid,signal.SIGKILL)
    code=proc.wait();c.update(status='INTERRUPTED',exit_code=code,seconds=time.monotonic()-start,error=f'{type(ex).__name__}: {ex}')
    f.flush();c['output_sha256']=sha(log);save();raise
  c.update(status='FINISHED',exit_code=code,seconds=time.monotonic()-start,output_sha256=sha(log));save();need(code==0 and not c.get('timed_out',False),'Command failed: '+label)
 try:
  for row in rows:
   for f,h in PINS.items():pin(PLAN/f,h)
   pin(TEMPLATE,TEMPLATE_SHA);pin(repo/TABLE_REL,TABLE_SHA)
   i=row['group'];U=unit(i);progress['active']=dict(group=i,stage='PREDECESSOR_VALIDATION');save();record(previous,i-1)
   if i>3:
    progress['active']['stage']='GENERATION';save()
    launch(f'group{i:02}-generate',[sys.executable,'-B',PLAN/'generate.py','--kind','next','--repo',repo,'--previous-record',previous,'--previous-inventory',unit(i-1)/'source-inventory.json','--depths',*map(str,row['depths']),'--output',U],120)
    launch(f'group{i:02}-bind-guard',[sys.executable,'-B',PLAN/'prepare_continuation_guard.py','--unit',U],30)
   static=inspect(row,previous,repo);write(out/f'group{i:02}-static.json',static);progress['active']['stage']='PREPARATION';progress['active']['static']=desc(out/f'group{i:02}-static.json');save()
   launch(f'group{i:02}-prepare',[sys.executable,'-B',U/'check.py','--repo',repo,'--output',U/'prepared1','--prepare-only'],60);record(U/'prepared1/verification.json',i,True)
   progress['active']['stage']='SOURCE_AND_AUDIT';save()
   launch(f'group{i:02}-proof',[sys.executable,'-B',U/'check.py','--repo',repo,'--output',U/'run1'],150)
   actual=record(U/'run1/verification.json',i);previous=U/'run1/verification.json'
   progress['completed'].append(dict(group=i,endpoint=row['endpoint'],record=desc(previous),preparation=desc(U/'prepared1/verification.json'),static=desc(out/f'group{i:02}-static.json'),warnings=actual['warnings'],seconds={c['label']:c['seconds']for c in actual['commands']}));save()
  need(len(progress['completed'])==7 and progress['completed'][-1]['endpoint']==407915,'Incomplete schedule')
  progress.update(status='PASS_COMPLETE_BOOTSTRAP_SCHEDULE',active=None,final_record=desc(previous),final_module=module(9),final_theorem='SetTheory.BusyBeaver.ZFC.BootRouting245Chunk009.bootstrap407915')
 except BaseException as ex:
  progress.update(status='STOPPED_FAILURE',error=f'{type(ex).__name__}: {ex}')
  # Preserve every partial output rather than synthesize a verification record.
  if progress['active']:
   U=unit(progress['active']['group']);progress['active']['available_records']=[desc(p)for p in [U/'prepared1/verification.json',U/'run1/verification.json']if p.is_file()]
  save();raise
 save();print(out/'coordination.json')
if __name__=='__main__':main()
