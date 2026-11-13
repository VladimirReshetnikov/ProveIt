#!/usr/bin/env python3
"""Execute actual runner main with isolated synthetic providers and fake compiler."""
import contextlib,hashlib,importlib.util,json,os,shutil,sys,tempfile,traceback
from pathlib import Path
ROOT=Path(__file__).resolve().parent
RUN=ROOT/'replay.py'; EXPECT='0c954807b7d8b75d299f4534a246c41fe541395b0d626a8a9a06ed9e512bd8e0'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,msg):
 if not x:raise ValueError(msg)
need(__debug__ and not sys.flags.optimize,'optimized Python rejected')
need(H(RUN)==EXPECT,'runner hash drift')
FAKE='''#!/usr/bin/python3
import os,re,sys
from pathlib import Path
root=Path(FAKE_ROOT);mode=(root/'mode').read_text(); args=sys.argv[1:]; lib=Path(os.environ['LEAN_PATH'].split(':')[0]);pkg=Path(os.environ['LEAN_PATH'].split(':')[1])
if '--deps' in args:
 src=Path(args[-1]); names=['Init']+re.findall(r'^import\\s+([\\w.]+)',src.read_text(),re.M)
 for dep in names:
  rel=Path(*dep.split('.')).with_suffix('.olean'); hits=[p for p in (lib/rel,pkg/rel) if p.is_file()]
  if not hits:sys.exit(12)
  print(hits[0])
 if mode=='wrong-deps':print(root/'unwanted.olean')
 sys.exit(0)
src=Path(next(x for x in args if x.endswith('.lean')));out=Path(args[args.index('-o')+1]); count=root/'count';n=int(count.read_text())+1 if count.exists() else 1;count.write_text(str(n)); out.parent.mkdir(parents=True,exist_ok=True)
if mode=='nonzero' and n==2:sys.exit(8)
if mode=='shadow-object' and n==1:(lib/'Init.olean').write_bytes(b'shadow')
if mode=='shadow-companion' and n==1:(lib/'Init.olean.private').write_bytes(b'shadow')
if mode=='package-companion' and n==1:(pkg/'Init.olean.private').write_bytes(b'extra')
if mode=='old-object-mutate' and n==2:(lib/'DiophantineConsistency/ArithmeticWangTableChunkBase.olean').write_bytes(b'changed')
if mode=='late-source-mutate' and n==3:(src.parent/'ArithmeticWangTableChunkBase.lean').write_text('changed')
if mode=='final-source-mutate' and n==96:(src.parent/'ArithmeticWangTableChunkBase.lean').write_text('changed')
if mode=='final-shadow-companion' and n==96:(lib/'Init.olean.private').write_bytes(b'late')
if mode=='final-old-object-mutate' and n==96:(lib/'DiophantineConsistency/ArithmeticWangTableChunkBase.olean').write_bytes(b'late')
if mode=='identical-source-symlink' and n==2:
 p=src.parent/'ArithmeticWangTableChunkBase.lean'; t=root/'same-source';t.write_bytes(p.read_bytes());p.unlink();p.symlink_to(t)
if mode=='redirect-directory' and n==1:
 old=out.parent; old.rename(root/'saved-project'); (root/'outside').mkdir();old.symlink_to(root/'outside',target_is_directory=True)
if mode=='symlink-output' and n==1:
 target=root/'outside-output';target.write_bytes(b'object');out.symlink_to(target)
elif mode!='missing-output' or n!=1:out.write_bytes(('fake-object-'+str(n)).encode())
if mode=='output-companion' and n==1:Path(str(out)+'.private').write_bytes(b'extra')
if mode=='warning' and n==2:print(str(src)+':1:1: warning: injected')
names=re.findall(r'^#print\\s+axioms\\s+([\\w.]+)\\s*$',src.read_text(),re.M)
for name in names:
 if mode=='missing-report' and n==2:continue
 ax='Unexpected.axiom' if mode=='extra-axiom' and n==2 else 'propext'
 print("'"+name+"' depends on axioms: ["+ax+"]")
 if mode=='duplicate-report' and n==2:print("'"+name+"' depends on axioms: [propext]")
'''
MON='''import os,subprocess
from pathlib import Path
def overlay(base,dest):
 for root,dirs,files in os.walk(base,followlinks=False):
  root=Path(root); target=dest/root.relative_to(base);target.mkdir(parents=True,exist_ok=True)
  for name in files:(target/name).symlink_to((root/name).resolve())
def monitored(cmd,env,log,timeout=120):
 with log.open('x') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
 return r.returncode,123456,None
'''
modes=['success','shadow-object','shadow-companion','package-companion','old-object-mutate','late-source-mutate','redirect-directory','symlink-output','missing-output','output-companion','nonzero','warning','wrong-deps','missing-report','extra-axiom','duplicate-report','identical-source-symlink','final-source-mutate','final-shadow-companion','final-old-object-mutate']
with tempfile.TemporaryDirectory(prefix='wang-full-fake-') as x:
 root=Path(x);results={}
 for mode in modes:
  case=root/mode;case.mkdir();seed=case/'seed';pkg=case/'package';seed.mkdir();pkg.mkdir();(seed/'DiophantineConsistency').mkdir();(pkg/'Init.olean').write_bytes(b'fake-init')
  for dep in ('ArithmeticMachineGraph215','WangTiles942TableData'):(seed/'DiophantineConsistency'/(dep+'.olean')).write_bytes(('fake-'+dep).encode())
  progress=case/'progress.json';progress.write_text(json.dumps({'steps':[{'compiler_exit':0} for _ in range(81)]+[{'compiler_exit':1}]}));pre=case/'preflight.json';pre.write_text('{}');original=case/'original.lean';original.write_text('fake-original');mon=case/'monitor.py';mon.write_text(MON);lean=case/'fake-lean';lean.write_text(FAKE.replace('FAKE_ROOT',repr(str(case))));lean.chmod(0o755);(case/'mode').write_text(mode)
  spec=importlib.util.spec_from_file_location('wang_runner_'+mode.replace('-','_'),RUN);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
  mod.SEED=seed;mod.PKG=pkg;mod.SEED_PROGRESS=progress;mod.SEED_PREFLIGHT=pre;mod.ORIGINAL=original;mod.MON=mon;mod.LEAN=lean
  mod.PINS=dict(mod.PINS,progress=H(progress),preflight=H(pre),original=H(original),monitor=H(mon),lean=H(lean))
  output=case/'out';old=sys.argv;sys.argv=['fake-control','--output',str(output)];failure=None
  with (case/'runner.stdout').open('w') as stdout,contextlib.redirect_stdout(stdout):
   try:mod.main()
   except Exception as exc:failure=repr(exc)
  sys.argv=old
  receipt=output/'RESULT.json';steps=json.loads((output/'progress.json').read_text())['steps'] if (output/'progress.json').exists() else []
  if mode=='success':
   need(failure is None and receipt.is_file() and len(steps)==96,('success failed',failure,len(steps)))
   data=json.loads(receipt.read_text());need(data['status']=='PASS_AUTHOR_ONLY_CHUNKED_TABLE' and len(data['steps'])==96,'fake receipt invalid')
   need(sum(len(x['axiom_reports']) for x in data['steps'])==94,'fake report inventory')
   need(all(x.get('compiler_command') and x.get('deps_command') and x.get('output_slots') for x in data['steps']),'missing per-child evidence')
   guard=data['final_direct_and_output_slots'];need(guard[str(output/'lib/Init.olean')] is None and guard[str(output/'lib/Init.olean.private')] is None and guard[str(pkg/'Init.olean')] is not None,'missing candidate-root guard')
  else:need(failure is not None and not receipt.exists(),('unexpected fake acceptance',mode,failure))
  results[mode]={'accepted':failure is None,'steps_seen':len(steps),'failure':failure}
 print(json.dumps({'status':'PASS_ISOLATED_96_CHILD_FAKE_WRAPPER','runner_sha256':EXPECT,'scope':'synthetic providers and fake compiler/monitor; no Lean, actual resource monitor or parent audit','cases':results},indent=2,sort_keys=True))
