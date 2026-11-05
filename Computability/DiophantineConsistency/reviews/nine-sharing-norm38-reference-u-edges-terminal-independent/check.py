import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38ReferenceUEdges'
cases={'check':('194a64bf3ddea7f7a3f41a6a24fac85a10179ea07e1cf9c2e47eac36414015d7','0dd718c2ef07f014c7170b647d383bc0f94cca0724bd559216c3c3002f0e3602',25957,1,'a85bfd113d0a9fceaa1453da6058d58284d9c358df57d00a35b06057b448c63f','6c5d2e14d142dad0023efefe975f013156997c15a8e43ef104ee173f3b1e069b',None),'retry01':('dbe89b1dd4d849a60008700d2d0274b227658643a3d8441c2159e4ae7e843290','10c30fb101db692c918c8e44ef4a0ef96306e5f804c75b00b03cbae68e649c24',34242,0,'4773e1b4fc40db5af78f58b6f8505b3b46ef71eb65966abb29dc82c68835bf11','10efe4bddb6d131f608b18d3fa4d230d041d70f7c53541a94a0ed33ae4a4d57b','7cb827b6b2ef7d5fb503106f7861daa2c8553a00823c798c18f63d2236421fdd')}
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
results={};sources={}
for tag,(sp,op,sess,exitcode,source,runner,obj) in cases.items():
 q=R/f'nine-sharing-norm38-reference-u-edges-{tag}';a=q/'attempt01';out=Path(f'/tmp/nine-sharing-norm38-reference-u-edges-{tag}-20261105');assert sha(a/'state.json')==sha(out/'state.json')==sp;s=json.loads((a/'state.json').read_text());assert s['status']==('PASS' if exitcode==0 else 'FAILED') and s['base_state_sha256']=='d3dc44f113f3cb6c176a67259b3d8df3c825a3ab9009f05374764ccddd7fb3ce' and sha(q/'run.py')==s['runner_sha256']==runner
 r=s['rows'][0];assert len(s['rows'])==1 and r['module']==n and r['source_sha256']==source
 src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,source);check(out/'src/DiophantineConsistency'/f'{n}.lean',source);sources[tag]=src.read_text()
 assert sha(a/'outer-terminal-author-record.json')==op;o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==sess and o['outer_exit_code']==exitcode and 'not independently observed' in o['observation_kind']
 for phase in ('deps','compile'):
  z=r[phase];assert z['exit']==(exitcode if phase=='compile' else 0) and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
  for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
 log=(a/f'{n}-compile.txt').read_text()
 if obj:
  assert r['object_sha256']==obj;check(out/'lib/DiophantineConsistency'/f'{n}.olean',obj);assert log.count('depends on axioms: [propext]')==3 and 'warning:' not in log and 'error:' not in log
 else:
  assert 'object_sha256' not in r and log.count('error: maximum recursion depth has been reached')==3 and log.count('sorryAx')==3
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
 dep=r['dependencies']['DiophantineConsistency.Norm38ReferenceBase'];assert dep['sha256']=='723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5';check(dep['path'],dep['sha256'],dep['realpath'])
 results[tag]={'author_recorded_session':sess,'author_recorded_exit':exitcode,'state_sha256':sp,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'object_sha256':obj}
assert sources['retry01']==sources['check'].replace('set_option maxHeartbeats 4000000\n','set_option maxHeartbeats 4000000\nset_option maxRecDepth 4096\n')
for eq in ('reference p x 78 = reference p x 77 + reference p x 75','reference p x 77 = reference p x 73 * reference p x 76','reference p x 76 = reference p x 74 - reference p x 75'):assert eq in sources['retry01']
p=D/'reviews/nine-sharing-norm38-reference-base-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','cases':results,'scope':'Three generic reference-node edge identities; no U identity or endpoint, no Lean replay.'},indent=2,sort_keys=True))
