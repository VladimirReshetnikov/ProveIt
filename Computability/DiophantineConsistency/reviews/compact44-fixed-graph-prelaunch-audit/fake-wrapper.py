import importlib.util,json,os,shutil,sys,tempfile,uuid
from pathlib import Path
from types import SimpleNamespace
root=Path(__file__).resolve().parents[4]
p=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-fixed-graph-digits-prototype/replay.py'
spec=importlib.util.spec_from_file_location('candidate',p);d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
scan=json.loads((d.PLAN/'scan.json').read_text()); modules=scan['modules']; selected={r['module'] for r in modules}; out=Path('/tmp/ipra-compact-fixed-graph-digits-pair-independent-'+uuid.uuid4().hex); scratch=Path(tempfile.mkdtemp(prefix='fixed-graph-fake-targets-'))
expected={'CompactMaskBounds':['bounds_of_residues'],'CompactBetaResidues':['residues'],'CompactMaskBoundFinish':['bounds'],'CompactFixedBeta':['beta_identity_generic','beta_identity','bounds'],'CompactSymbolicPorts':['graph_digits_of_symbols','graph_digits'],'CompactGenericGraphDigits':['graph_digits','fixed_graph_digits']}
case=sys.argv[1]; calls={'comp':0,'deps':0,'verify':0}
class Fake:
 def overlay(self,base,lib):
  lib.mkdir(parents=True)
  for row in modules:
   for imp in row['imports']:
    if imp not in selected:
     obj=(lib/Path(*imp.split('.'))).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(b'parent-object')
  if case=='collision':
   obj=(lib/Path(*modules[0]['module'].split('.'))).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(b'collision')
 def monitored(self,cmd,env,log):
  calls['comp']+=1;n=Path(cmd[-3]).stem;outobj=Path(cmd[-1]);outobj.parent.mkdir(parents=True,exist_ok=True)
  lib=Path(env['LEAN_PATH'].split(':')[0]);parent=lib/'DiophantineConsistency/CompactSymbolicGraphDigits.olean'
  if case=='dependency_mutation' and calls['comp']==1:parent.write_bytes(b'changed')
  if case=='companion_creation' and calls['comp']==1:Path(str(parent)+'.private').write_bytes(b'new')
  if case=='output_mutation' and calls['comp']==2:(lib/'DiophantineConsistency/CompactMaskBounds.olean').write_bytes(b'changed-output')
  if case=='late_source_drift' and calls['comp']==8:(out/'frozen/DiophantineConsistency/CompactMaskBounds.lean').write_text('late altered')
  if case=='frozen_symlink' and calls['comp']==8:
   q=out/'frozen/DiophantineConsistency/CompactMaskBounds.lean';target=scratch/'same-source.lean';target.write_bytes(q.read_bytes());q.unlink();q.symlink_to(target)
  if case=='symlink_output':
   target=scratch/(n+'.olean');target.write_bytes(n.encode());outobj.symlink_to(target)
  elif case!='missing_output':outobj.write_bytes((n+('bad' if case=='sibling_mismatch' and calls['comp']>6 else '')).encode())
  names=expected[n];reports=["'%s.%s' depends on axioms: [propext, Classical.choice, Quot.sound]"%(n,x) for x in names]
  if case=='wrong_report':reports[0]=reports[0].replace(n+'.',n+'.wrong_')
  if case=='wrong_axiom':reports[0]=reports[0].replace('Quot.sound','Classical.choice')
  if case=='warning':reports.append('warning: simulated')
  if case=='sorry':reports.append('sorryAx')
  log.write_text('\n'.join(reports)+'\n')
  if case=='source_drift':Path(cmd[-3]).write_text('changed')
  return (1 if case=='compiler_exit' else 0,123,None if case!='stop_reason' else 'simulated')
fake=Fake();d.load=lambda p:fake
review={'evidence_commit':'fake','receipt_sha256':'fake'}
def verify():
 calls['verify']+=1
 return scan, (dict(review,drift=1) if case=='parent_drift' and calls['verify']>1 else review)
d.verify=verify
class Res:
 returncode=0;stderr=''
def run(cmd,env=None,**kw):
 if '--deps' not in cmd:raise RuntimeError('unexpected subprocess '+repr(cmd))
 calls['deps']+=1;src=Path(cmd[-1]);imports=[j for l in src.read_text().splitlines() if l.startswith('import ') for j in l[7:].split()];lib=Path(env['LEAN_PATH'].split(':')[0]);paths=[str(d.PACKAGE/'Init.olean')]+[str((lib/Path(*x.split('.'))).with_suffix('.olean')) for x in imports]
 if case=='missing_required' or (case=='missing_required_6' and calls['deps']==6) or (case=='missing_required_12' and calls['deps']==12):Path(paths[-1]).unlink()
 r=Res();r.stdout='\n'.join(paths if case!='wrong_deps' else paths[:-1])+'\n';r.returncode=1 if case=='deps_exit' else 0;r.stderr='simulated' if case=='deps_stderr' else ''
 return r
d.subprocess.run=run
if os.path.lexists(out):raise RuntimeError('fresh test path collision')
sys.argv=[str(p),'--output',str(out)]
try:
 d.main();accepted=True;err=''
except Exception as e:
 accepted=False;err=type(e).__name__+': '+str(e)[:350]
finally:
 if out.exists():shutil.rmtree(out)
 shutil.rmtree(scratch)
if accepted != (case=='good'):raise RuntimeError(('unexpected result',case,accepted,err,calls))
if case=='good' and (calls['comp']!=12 or calls['deps']!=12):raise RuntimeError(('wrong loop counts',calls))
print(json.dumps({'case':case,'accepted':accepted,'calls':calls,'error':err}))
