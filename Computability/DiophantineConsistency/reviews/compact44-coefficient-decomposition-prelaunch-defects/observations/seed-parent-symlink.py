#!/usr/bin/env python3
"""Fake paired full-loop checks, without Lean or real parent audits."""
import contextlib,hashlib,importlib.util,io,json,os,shutil,subprocess,sys,tempfile,types
from pathlib import Path
D=Path(__file__).with_name('replay-reviewed-735a.py');HEAD='a'*40
MODES=['seed_parent_symlink']
for mode in MODES:
 spec=importlib.util.spec_from_file_location('candidate',D);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 root=Path(tempfile.mkdtemp(prefix='coeff-fake-fixture-',dir='/tmp'));out=Path(tempfile.mkdtemp(prefix='ipra-compact-coefficient-decomposition-pair-fake-',dir='/tmp'));out.rmdir()
 m.SOURCE=root/'input.lean';m.SOURCE.write_text('import Example\n');m.PINS={m.SOURCE:hashlib.sha256(m.SOURCE.read_bytes()).hexdigest()};m.CLOSURE_PINS={};m.PREFIX=root/'providers';m.PACKAGE=root/'package';m.PACKAGE.mkdir();(m.PACKAGE/'Init.olean').write_bytes(b'init')
 seeds=[]
 for side in ('author','peer'):
  (m.PREFIX/side/'lib/DiophantineConsistency').mkdir(parents=True);(m.PREFIX/side/'lib/DiophantineConsistency/ArithmeticWindowCarry.olean').write_bytes(b'window')
  for name in ('Compact943Decoder','CompactCoefficientMass'):
   p=root/(side+'-'+name+'.olean');p.write_bytes(name.encode());seeds.append({'side':side,'module':name,'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 if mode=='missing_seed':Path(seeds[0]['path']).unlink()
 if mode=='seed_companion':Path(seeds[0]['path']+'.private').write_bytes(b'injected')
 scan={'seeds':seeds};counts={'head':0,'verify':0,'deps':0,'child':0}
 def head():
  counts['head']+=1;return 'b'*40 if mode=='head_drift' and counts['head']>1 else HEAD
 m.head=head
 def verify():
  counts['verify']+=1
  if counts['verify']>1:
   if mode=='late_source':(out/'frozen/DiophantineConsistency/CompactCoefficientDecoder.lean').write_text('changed')
   if mode=='late_seed':Path(seeds[0]['path']).write_bytes(b'changed')
   if mode=='late_output':(out/'author/lib/DiophantineConsistency/CompactCoefficientDecoder.olean').write_bytes(b'changed')
   if mode=='late_log':(out/'author/compiler.log').write_text('changed')
   if mode=='late_companion':(out/'author/lib/DiophantineConsistency/CompactCoefficientDecoder.olean.private').write_bytes(b'injected')
  return scan,[{'v':1 if mode!='parent_drift' or counts['verify']==1 else 2}]
 m.verify=verify
 def overlay(base,lib):
  d=lib/'DiophantineConsistency';d.parent.mkdir(parents=True);outside=root/'outside';outside.mkdir(exist_ok=True);d.symlink_to(outside,target_is_directory=True);(d/'ArithmeticWindowCarry.olean').symlink_to(base/'DiophantineConsistency/ArithmeticWindowCarry.olean')
  if mode=='seed_collision':(d/'Compact943Decoder.olean.private').write_bytes(b'injected')
  if mode=='output_collision':(d/'CompactCoefficientDecoder.olean.server').write_bytes(b'injected')
 def monitored(cmd,env,log,timeout):
  counts['child']+=1;obj=Path(cmd[-1]);src=Path(cmd[-3]);obj.write_bytes(b'peer' if mode=='sibling_mismatch' and 'peer' in str(obj) else b'object')
  if mode=='output_symlink':
   obj.unlink();back=obj.with_suffix('.backing');back.write_bytes(b'object');obj.symlink_to(back)
  if mode=='output_missing':obj.unlink()
  if mode=='output_companion' or mode=='peer_companion' and 'peer' in str(obj):Path(str(obj)+'.private').write_bytes(b'injected')
  if mode=='frozen_symlink':
   raw=src.read_bytes();src.unlink();back=src.with_suffix('.backing');back.write_bytes(raw);src.symlink_to(back)
  names=sorted(m.REPORTS)
  if mode=='wrong_report':names[0]='wrong.name'
  if mode=='missing_report':names.pop()
  if mode=='extra_report':names.append('extra.name')
  ax='propext' if mode=='wrong_axiom' else 'propext, Classical.choice, Quot.sound'
  text=''.join("'"+n+"' depends on axioms: ["+ax+"]\n" for n in names)
  if mode=='warning':text+='warning: injected\n'
  if mode=='sorry':text+='sorryAx\n'
  log.write_text(text)
  return (True if mode=='boolean_exit' else 1 if mode=='nonzero' else 0),100,('stop' if mode=='stop' else None)
 m.importlib=types.SimpleNamespace(util=types.SimpleNamespace(spec_from_file_location=lambda *a:None,module_from_spec=lambda *a:types.SimpleNamespace(overlay=overlay,monitored=monitored)))
 class Loader:
  def exec_module(self,obj):pass
 m.importlib.util.spec_from_file_location=lambda *a:types.SimpleNamespace(loader=Loader())
 def run(cmd,env=None,**kw):
  counts['deps']+=1;lib=Path(env['LEAN_PATH'].split(':')[0]);init=str(m.PACKAGE/'Init.olean')
  paths=[init]+[str(lib/'DiophantineConsistency'/(name+'.olean')) for name in ('ArithmeticWindowCarry','Compact943Decoder','CompactCoefficientMass')]
  if mode=='wrong_dep':paths.append('/tmp/wrong.olean')
  if mode=='duplicate_dep':paths.append(paths[1])
  if mode=='duplicate_init':paths.append(init)
  if mode=='triple_init':paths.extend([init,init])
  if mode=='missing_init':Path(init).unlink()
  if mode=='missing_direct':Path(paths[1]).unlink()
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(paths)+'\n',stderr='')
 m.subprocess=types.SimpleNamespace(run=run);m.shutil=types.SimpleNamespace(copyfile=shutil.copyfile,disk_usage=lambda _:types.SimpleNamespace(free=10*1024**3))
 sys.argv=[str(D),'--expected-head',HEAD,'--verify-only'] if mode=='verify_only' else [str(D),'--expected-head',HEAD,'--output',str(out)]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();err=None
   except Exception as e:err=str(e)
  if mode=='seed_parent_symlink':
   assert err is not None and 'invalid output directory' in err and (root/'outside/Compact943Decoder.olean').is_file() and (root/'outside/CompactCoefficientMass.olean').is_file(),(mode,err)
  elif mode=='verify_only':assert err is None and counts['child']==0 and not out.exists(),(mode,err,counts)
  elif mode in ('good','duplicate_init'):assert err is None and counts['child']==2,(mode,err,counts)
  else:
   expected={'triple_init':'dependency mismatch','wrong_dep':'dependency mismatch','duplicate_dep':'dependency mismatch','missing_init':'companion drift','missing_direct':'companion drift','missing_seed':'seed drift','seed_companion':'seed companion','seed_collision':'seed collision','output_collision':'unexpected output companion','output_companion':'unexpected output companion','peer_companion':'unexpected output companion','output_symlink':'invalid output','output_missing':'invalid output','warning':'compiler failure','sorry':'compiler failure','wrong_report':'axiom reports','wrong_axiom':'axiom reports','missing_report':'axiom reports','extra_report':'axiom reports','nonzero':'compiler failure','boolean_exit':'compiler failure','stop':'compiler failure','sibling_mismatch':'paired output mismatch','frozen_symlink':'frozen source drift','late_source':'frozen source drift','late_seed':'companion drift','late_output':'companion drift','late_log':'final output drift','late_companion':'unexpected companion','parent_drift':'final input drift','head_drift':'preflight drift'}[mode]
   assert err is not None and expected in err,(mode,expected,err,counts)
  print(mode,'PASS',counts['child'],'fake children')
 finally:shutil.rmtree(root,ignore_errors=True);shutil.rmtree(out,ignore_errors=True)

for suffix in (x for x in m.SUFFIXES if x != '.olean'):
 with tempfile.TemporaryDirectory(prefix='coeff-output-slot-',dir='/tmp') as td:
  obj=Path(td)/'X.olean';comp=Path(str(obj)[:-6]+suffix);comp.write_bytes(b'injected')
  for before in (True,False):
   if not before:obj.write_bytes(b'object')
   try:m.output(obj,before)
   except ValueError as e:assert 'unexpected output companion' in str(e),(suffix,before,str(e))
   else:raise AssertionError((suffix,before))
print('all_nine_output_companion_slots_before_and_after PASS')
