import copy,importlib.util,json,os,shutil,sys,tempfile,uuid
from pathlib import Path
from types import SimpleNamespace
root=Path(__file__).resolve().parents[4];p=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-clean-carry-reset-prototype/replay.py';sp=importlib.util.spec_from_file_location('candidate',p);d=importlib.util.module_from_spec(sp);sp.loader.exec_module(d)
scan=copy.deepcopy(json.loads((d.PLAN/'scan.json').read_text())); scratch=Path(tempfile.mkdtemp(prefix='clean-carry-fake-targets-'));case=sys.argv[1];out=Path('/tmp/ipra-compact-clean-carry-pair-independent-'+uuid.uuid4().hex);calls={'comp':0,'deps':0,'verify':0}
for seed in scan['seeds']:
 src=Path(seed['source']);new=scratch/seed['side']/'CompactHeterogeneousCarry.olean';new.parent.mkdir();shutil.copyfile(src,new);seed['source']=str(new)
if case=='seed_companion':Path(scan['seeds'][0]['source']+'.private').write_bytes(b'extra')
class Fake:
 def overlay(self,base,lib):
  lib.mkdir(parents=True)
  if case=='output_collision':
   t=lib/'DiophantineConsistency/CompactCarryReset.olean.private';t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(b'bad')
  if case=='seed_collision':
   t=lib/'DiophantineConsistency/CompactHeterogeneousCarry.olean.private';t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(b'bad')
 def monitored(self,cmd,env,log):
  calls['comp']+=1;src=Path(cmd[-3]);obj=Path(cmd[-1]);obj.parent.mkdir(parents=True,exist_ok=True)
  if case=='output_symlink':
   target=scratch/'fake.olean';target.write_bytes(b'obj');obj.symlink_to(target)
  elif case!='missing_output':obj.write_bytes(b'peer' if case=='peer_mismatch' and calls['comp']==2 else b'obj')
  if case=='output_companion':Path(str(obj)+'.private').write_bytes(b'extra')
  if case=='late_source_drift' and calls['comp']==2:src.write_text('changed')
  if case=='frozen_symlink' and calls['comp']==2:
   target=scratch/'same.lean';target.write_bytes(src.read_bytes());src.unlink();src.symlink_to(target)
  if case=='seed_mutation' and calls['comp']==1:(Path(env['LEAN_PATH'].split(':')[0])/'DiophantineConsistency/CompactHeterogeneousCarry.olean').write_bytes(b'bad')
  if case=='seed_companion_creation' and calls['comp']==1:(Path(env['LEAN_PATH'].split(':')[0])/'DiophantineConsistency/CompactHeterogeneousCarry.olean.private').write_bytes(b'extra')
  text=d.EXPECTED
  if case=='wrong_report':text=text.replace('digit_after_bounded_predecessor','wrong_name')
  if case=='wrong_axiom':text=text.replace('Quot.sound','Classical.choice',1)
  if case=='warning':text+='warning: test\n'
  if case=='sorry':text+='sorryAx\n'
  log.write_text(text);return (1 if case=='compiler_exit' else 0,123,'stopped' if case=='stop_reason' else None)
d.load=lambda _:Fake();parent={'status':'fake'}
def verify():
 calls['verify']+=1
 if case=='parent_drift' and calls['verify']>1:return scan,{'status':'changed'}
 if case=='final_output_companion' and calls['verify']>1:(out/'author/lib/DiophantineConsistency/CompactCarryReset.olean.private').write_bytes(b'late')
 if case=='final_source_drift' and calls['verify']>1:(out/'frozen/DiophantineConsistency/CompactCarryReset.lean').write_text('late')
 return scan,parent
d.verify=verify
class Res: returncode=0;stderr=''
def run(cmd,env=None,**kw):
 assert '--deps' in cmd;calls['deps']+=1;lib=Path(env['LEAN_PATH'].split(':')[0]);seed=lib/'DiophantineConsistency/CompactHeterogeneousCarry.olean';paths=[str(d.PACKAGE/'Init.olean'),str(seed)]
 if case=='missing_required':seed.unlink()
 r=Res();r.stdout='\n'.join(paths if case!='wrong_deps' else paths[:1])+'\n';r.returncode=1 if case=='deps_exit' else 0;r.stderr='bad' if case=='deps_stderr' else '';return r
d.subprocess.run=run
if os.path.lexists(out):raise RuntimeError('fresh path collision')
sys.argv=[str(p),'--output',str(out)]
try:
 d.main();accepted=True;err=''
except Exception as e:
 accepted=False;err=type(e).__name__+': '+str(e)[:350]
finally:
 if out.exists():shutil.rmtree(out)
 shutil.rmtree(scratch)
if accepted!=(case=='good'):raise RuntimeError(('unexpected fake result',case,accepted,err,calls))
if case=='good' and (calls['comp']!=2 or calls['deps']!=2):raise RuntimeError(('wrong counts',calls))
print(json.dumps({'case':case,'accepted':accepted,'calls':calls,'error':err}))
