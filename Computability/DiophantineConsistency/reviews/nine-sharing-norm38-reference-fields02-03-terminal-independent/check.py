import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent; D=P.parents[1]; R=D/'research'; sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
cases={'02':('14c311304266f76b615db854d4f9c77d5236614ce4c68a3ddf2933a47727f729','6aabaffdbe29181ca0f770d67715f235cbb69335b4b32adbbf2010673840f24b',27001,'d4b1bccc444a1e87e10cc2ab95c356e304be2b9666244a6d1322deab2aadef54','879bf960105fe38d61d4f74aaf4210a745b94bc2d264fbd06a5f58bf50acf2ac'),'03':('7c525a6a51c6d780c5615b3d64d607f8764203581036a0e9b5b6f5ae3f3b2578','1427049f45ee9aff0ee769a4ffe84d1bceda74aad6be6c7d330d15884844501a',15469,'7fcd23b2c5d32ead949e1a2e640c59041bcd8a6a948a8c7bf45497b342beb153','fd181963ef0a76645ec06569e8f805061a0639a334be1f154daf85e6192ff4fb')}
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
results={}
for n,(state_pin,outer_pin,session,source_pin,runner_pin) in cases.items():
 q=R/f'nine-sharing-norm38-reference-fields{n}-check';a=q/'attempt01';out=Path(f'/tmp/nine-sharing-norm38-reference-fields{n}-check-20261105');module=f'Norm38ReferenceFields{n}'
 assert sha(a/'state.json')==sha(out/'state.json')==state_pin
 s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']==f"RuntimeError('compile failed {module}')" and s['base_state_sha256']=='d3dc44f113f3cb6c176a67259b3d8df3c825a3ab9009f05374764ccddd7fb3ce'
 assert sha(q/'run.py')==s['runner_sha256']==runner_pin and "'-M2800'" in (q/'run.py').read_text()
 assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==module and r['source_sha256']==source_pin and 'object_sha256' not in r
 assert sha(q/'src/DiophantineConsistency'/f'{module}.lean')==sha(out/'src/DiophantineConsistency'/f'{module}.lean')==source_pin
 assert not (out/'lib/DiophantineConsistency'/f'{module}.olean').exists()
 assert sha(a/'outer-terminal-author-record.json')==outer_pin
 o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==session and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
 for phase in ('deps','compile'):
  z=r[phase];assert z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'] and z['rss_limit_bytes']==4*1024**3
  for path in (a,out):check(path/f'{module}-{phase}.txt',z['log_sha256'])
 assert r['deps']['exit']==0 and r['compile']['exit']==-6
 log=(a/f'{module}-compile.txt').read_text();assert 'lean::memory_exception' in log and "at 'interpreter'" in log and 'depends on axioms' not in log
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
 for mod,h in {'Carrier65':'10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f','Norm38ReferenceBase':'723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5'}.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath'])
 results[n]={'author_recorded_session':session,'author_recorded_exit':1,'state_sha256':state_pin,'lean_exit':-6,'sampled_peak_session_rss_bytes':r['compile']['peak_session_rss_bytes'],'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links'])}
# Recheck direct producer provenance through the independent successful P/Q review.
p=D/'reviews/nine-sharing-norm38-reference-fields01-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_FAILURE_EVIDENCE_ONLY','cases':results,'scope':'Retained point checks and provider review; author records of outer exits, no Lean replay, no final postflight or theorem success.'},indent=2,sort_keys=True))
