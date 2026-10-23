"""Owned two-probe direct profile comparison. Source draft; root reviews before execution."""
from pathlib import Path
import argparse,fcntl,hashlib,importlib.util,json,os,re,signal
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
B=Path('/tmp/k215-phase24-check-v3/candidate-build-run1')
BP=Path('/tmp/k215-phase24-check-v3/candidate-plan.json')
BSHA='c9bcee3023ea879ad0dcc353d1435aae8aef92963a4b79f51fda1506f518c910'
BPSHA='4bda49c298304608bd3196d92a3c748140142e8a649708102d827e690f489505'
SUP=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
SUPSHA='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LEANSHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
LOCK=Path('/tmp/proveit-k215-proof-build.lock')
OLD='6d61edd50c7062213be2e34a3b6a1efdb67d0f8072e75d4ff5dea20b41f549be'
NEW='448229ba92adad5d79c52ee6e2ac32cecf75c0074196e36c5fa8f9d2b9188804'
FOL='84add1e8222f9f655e1dc252a826914623238b8e3e8169d18ed39f740b2bbacd'
NAMES=['SetTheory.'+n for n in ['cons_sub','mem_map_sub','map_rename_up_S','Prov_rename','generalize_fresh','Prov_cut','soundness']]
STD={'propext','Classical.choice','Quot.sound'}
REPORT=re.compile(r"'([^'\r\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def save(p,x):
 with Path(p).open('x')as f:json.dump(x,f,indent=2);f.write('\n')
def profiles(text):
 result=[];position=0
 for match in REPORT.finditer(text):
  assert not text[position:match.start()].strip(),'Unexpected compiler output'
  raw=match.group(2)
  axioms=[] if raw is None or not raw.strip() else [a.strip()for a in raw.split(',')]
  assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',a)for a in axioms)
  assert len(axioms)==len(set(axioms))and set(axioms)<=STD
  result.append([match.group(1),axioms]);position=match.end()
 assert not text[position:].strip()and [n for n,_ in result]==NAMES
 return result

def main():
 p=argparse.ArgumentParser()
 for name in ['new-check','new-plan','out']:p.add_argument('--'+name,type=Path,required=True)
 for name in ['new-plan-sha','new-result-sha']:p.add_argument('--'+name,required=True)
 a=p.parse_args();assert not a.out.exists()and not a.out.is_symlink()
 probe=Path(__file__).resolve().with_name('CalculusProfiles.lean')
 assert probe.read_text()=='import FirstOrder.Calculus\n\n'+''.join('#print axioms '+n+'\n'for n in NAMES)
 bindings={}
 def pin(path,expected=None):
  path=Path(path).absolute();h=sha(path)
  if expected is not None:assert h==expected,path
  if str(path)in bindings:assert bindings[str(path)]==h,path
  bindings[str(path)]=h;return h
 pin(__file__);pin(probe);pin(SUP,SUPSHA);pin(LEAN,LEANSHA);pin(BP,BPSHA)
 oldplan=read(BP);newplan=read(a.new_plan);pin(a.new_plan,a.new_plan_sha)
 assert newplan['mode']=='phase25-focused-elaboration'and newplan['status']=='SOURCE_DERIVED_FOCUSED_ELABORATION_NOT_FULL'
 assert newplan['basis_directory']==str(B)and newplan['basis_result_sha256']==BSHA
 assert newplan['base_commit']=='593c05920f751e6696fd2bc9bb583225b128f359'and newplan['audits']==[]
 metadata={};closures={};toolchain=None
 for side,directory,plan,resultsha,sourcehash in [('old',B,oldplan,BSHA,OLD),('new',a.new_check,newplan,a.new_result_sha,NEW)]:
  directory=directory.resolve();pin(directory/'result.json',resultsha);result=read(directory/'result.json')
  assert result['status']=='PASS'and result['map_sha256']==pin(BP if side=='old'else a.new_plan)
  pin(directory/'inventory.json',result['inventory_sha256']);pin(directory/'completed.json',result['completed_sha256'])
  inv=read(directory/'inventory.json');done=read(directory/'completed.json');rows={r['module']:r for r in inv['modules']}
  assert inv['modules']==plan['modules']and len(rows)==len(inv['modules'])==len(done)==result['provider_count']and set(rows)==set(done)
  if side=='old':assert len(rows)==230
  pin(directory/'toolchain.json');tc=read(directory/'toolchain.json')
  if toolchain is None:toolchain=tc
  else:assert tc==toolchain
  for key in ['lean','lake','Init.olean','project_toolchain']:pin(tc[key]['path'],tc[key]['sha256'])
  assert tc['lean']['path']==str(LEAN)and tc['lean']['sha256']==LEANSHA
  selected={}
  def visit(m):
   if m=='Init'or m in selected:return
   assert m in {'FirstOrder.Fol','FirstOrder.Calculus'}
   row=rows[m];rec=done[m];assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
   rel=m.replace('.','/');src=directory/'workspace'/(rel+'.lean');obj=directory/'objects'/(rel+'.olean')
   expected=FOL if m=='FirstOrder.Fol'else sourcehash
   pin(src,expected);assert row['source_sha256']==rec['source_sha256']==expected
   pin(obj,rec['object_sha256']);pin(rec['log'],rec['log_sha256'])
   assert not any(s in Path(rec['log']).read_text()for s in ['warning:','error:','sorryAx'])
   assert row['imports']==([]if m=='FirstOrder.Fol'else['FirstOrder.Fol'])
   assert rec['dependencies']=={d:done[d]['object_sha256']for d in row['imports']}
   selected[m]={'source':str(src),'source_sha256':expected,'object':str(obj),'object_sha256':rec['object_sha256'],'dependencies':rec['dependencies']}
   for parent in row['imports']:visit(parent)
  visit('FirstOrder.Calculus');assert set(selected)=={'FirstOrder.Fol','FirstOrder.Calculus'}
  closures[side]=selected;metadata[side]={'directory':str(directory),'result_sha256':resultsha,'plan_sha256':pin(BP if side=='old'else a.new_plan)}
 assert closures['old']['FirstOrder.Fol']['object_sha256']==closures['new']['FirstOrder.Fol']['object_sha256']
 a.out.mkdir();runs={}
 with(a.out/'output.lock').open('x')as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  save(a.out/'before.json',{'inputs':bindings,'probe_sha256':sha(probe),'closures':closures,'metadata':metadata})
  spec=importlib.util.spec_from_file_location('owned_calculus_profile_supervisor',SUP);supervisor=importlib.util.module_from_spec(spec);spec.loader.exec_module(supervisor)
  for side in ['old','new']:
   folder=a.out/side;folder.mkdir();obj=folder/'CalculusProfiles.olean';log=folder/'compiler.log';raw=folder/'record.json'
   env=os.environ.copy();env['LEAN_PATH']=str(Path(metadata[side]['directory'])/'objects');env['LEAN_NUM_THREADS']='1'
   command=[str(LEAN),'-j1','-M12288','--root='+str(probe.parent),'-o',str(obj),str(probe)]
   row={'module':'CalculusProfiles','source':str(probe),'source_sha256':sha(probe),'command':command,'lean_path':env['LEAN_PATH'],'compiler_sha256':LEANSHA,'helper_sha256':SUPSHA,'dependencies':{m:r['object_sha256']for m,r in closures[side].items()},'timeout_seconds':120,'memory_mebibytes':12288,'basis':metadata[side]}
   print('PROBE',side,flush=True);ok=supervisor.run_locked(command,probe.parent,env,LOCK,log,120,row,raw)
   text=log.read_text();assert ok and row['exit_code']==0 and not row['timed_out']and not any(s in text for s in ['warning:','error:','sorryAx'])
   runs[side]={'record_sha256':sha(raw),'log_sha256':sha(log),'object_sha256':sha(obj),'seconds':row['seconds'],'profiles':profiles(text)}
   for path,h in bindings.items():assert sha(path)==h,path
  for side in ['old','new']:
   for name,key in [('record.json','record_sha256'),('compiler.log','log_sha256'),('CalculusProfiles.olean','object_sha256')]:assert sha(a.out/side/name)==runs[side][key]
  same=runs['old']['profiles']==runs['new']['profiles']
  save(a.out/'comparison.json',{'status':'PASS_EXACT_ORDERED_PROFILES'if same else'FAIL_PROFILE_DISCREPANCY','same_probe_sha256':sha(probe),'runs':runs,'metadata':metadata,'all_inputs_postchecked':True,'scope':'Seven direct public declaration profiles only. Two fresh identical probes import separate old accepted/new focused objects. No dependency recompilation,full endpoint acceptance or performance claim.'})
  assert same,'Exact old/new ordered axiom profiles differ; original logs retained.'
  print('PASS_EXACT_ORDERED_PROFILES',sha(a.out/'comparison.json'),flush=True)
if __name__=='__main__':
 def interrupted(signum,frame):raise KeyboardInterrupt(f'Signal {signum}')
 signal.signal(signal.SIGTERM,interrupted)
 main()
