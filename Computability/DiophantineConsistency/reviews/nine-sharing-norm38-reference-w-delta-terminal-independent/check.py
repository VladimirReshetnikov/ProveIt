import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
cases={'w':('Norm38ReferenceW','4850cac5e7763883617255c554d743e82a0c91a6f07f2b69d63432ff07b75a96','216d744991998872160a608fbf00b1a6f1e19465ca6ba289888d780866b906ff',27053,'e46712b893bf85dc33c3a184811c3c477a95bc6fb977bb176e9354ee1178e916','903a876c8f16adf6a3452fb6bfacf08d5167280c20d7636acbe0d90b4cb74fe6','113d3d8021fe7b40ca19f7fca5eedbecf0b8ae87af6ab5d2de188f777775cbdb','reference_W',2),'delta':('Norm38ReferenceDelta','3f4fd6ae49b2a4a3da22e07849205f55ca9012bb14c2ee8c09297907d598aa2b','d954c422ee1f8f9aa5564c0b4bc2410e9570c72244f0bd7ea131dcddf607cb2b',84469,'f9705206caaa688d1e1665be50446715b8017328d8875585fe92b1c2bc76eef9','de52874280b09577f07fa2c359f4f3e4e53cf166ed3cde161109f9991bbc8d6d','d43d2cbdd4e19edad31de95b48e51ba1459a4cdc61a286e742d8279e01292a65','reference_delta',1)}
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
results={}
for name,(module,state_pin,outer_pin,session,source_pin,runner_pin,object_pin,thm,warnings) in cases.items():
 q=R/f'nine-sharing-norm38-reference-{name}-check';a=q/'attempt01';out=Path(f'/tmp/nine-sharing-norm38-reference-{name}-check-20261105')
 assert sha(a/'state.json')==sha(out/'state.json')==state_pin;s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='d3dc44f113f3cb6c176a67259b3d8df3c825a3ab9009f05374764ccddd7fb3ce'
 assert sha(q/'run.py')==s['runner_sha256']==runner_pin
 assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==module and r['source_sha256']==source_pin and r['object_sha256']==object_pin
 assert sha(q/'src/DiophantineConsistency'/f'{module}.lean')==sha(out/'src/DiophantineConsistency'/f'{module}.lean')==source_pin;check(out/'lib/DiophantineConsistency'/f'{module}.olean',object_pin)
 assert sha(a/'outer-terminal-author-record.json')==outer_pin;o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==session and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
 for phase in ('deps','compile'):
  z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
  for path in (a,out):check(path/f'{module}-{phase}.txt',z['log_sha256'])
 log=(a/f'{module}-compile.txt').read_text();assert log.count('warning:')==warnings and f"'DiophantineConsistency.Norm38Reference.{thm}' depends on axioms: [propext]" in log and 'error:' not in log
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
 for mod,h in {'Carrier65':'10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f','Norm38ReferenceBase':'723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5'}.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath'])
 results[name]={'author_recorded_session':session,'author_recorded_exit':0,'state_sha256':state_pin,'object_sha256':object_pin,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'warnings':warnings,'axioms':['propext']}
p=D/'reviews/nine-sharing-norm38-reference-fields01-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','cases':results,'scope':'Retained point checks and producer review; author records of outer exits, no Lean replay or full dynamic ancestry.'},indent=2,sort_keys=True))
