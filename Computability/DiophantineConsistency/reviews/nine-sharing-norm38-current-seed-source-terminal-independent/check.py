import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-seed-source-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-seed-source-check-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='20c2e1ba07a2131cee639d2e872498a006ce150d22f72ba0cab7fcec3342a64c';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='9bef14e22cf04c4a9b0810dcd71866c40401a1f49d369e068151dfe2b111ce59'
assert sha(q/'run.py')==s['runner_sha256']=='6ce71783221031646266888b484404ae3a1926a1a52a21c505c2bd162efc2d79' and sha(q/'source-manifest.json')=='60a4658bd4ccf35868962afec2517a3448d66bc60302b185989da39ebf5de2ac' and sha(q/'provider_preflight.py')=='52cd5c208320f64d809e0ca6731cf00b349080a045fd052c7fa41d87268d408d'
assert sha(a/'outer-terminal-author-record.json')=='c63afa1a51dd78779c0973c63b4fb4ba015910201e3e0fdcfaf6032b163ceac4';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==96515 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
rows=s['rows'];names=['Norm38FourCastSeedSource','Norm38CurrentSeedSource'];objects=['aae347ab5836a894a43ec1cd7defc37b61fd505369c756f489b57a3e322e994b','176750b96fc712e1827066d61958dd164852427587d599d5846aeec4d1207d10'];assert [r['module'] for r in rows]==names;m=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(m)==2
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for i,r in enumerate(rows):
 n=r['module'];assert r['source_sha256']==m[i]['source_sha256'] and r['object_sha256']==objects[i];check(q/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
 for phase in ('deps','compile'):
  z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
  for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for mod,v in r['dependencies'].items():check(v['path'],v['sha256'],v['realpath']);assert r['direct_guard'][v['path']]['sha256']==v['sha256'] and r['direct_guard'][v['path']]['realpath']==v['realpath']
 log=(a/f'{n}-compile.txt').read_text();assert 'depends on axioms: [propext,\n Classical.choice,\n Quot.sound]' in log and 'warning:' not in log and 'error:' not in log
assert rows[0]['dependencies']['DiophantineConsistency.Norm38SeedSource']['sha256']=='e4a4092b123ed7dd0b3c6c2d7e88af9447ca3f1a941ded0dba3f656a1edfd766';assert rows[1]['dependencies']['DiophantineConsistency.Norm38FourCastSeedSource']['sha256']==objects[0]
inv=json.loads((q/'survey-result.json').read_text());assert inv['shared_count']==1107 and len(inv['b_only'])==8
for name in ['Norm38FourVariablePorts']+[f'Norm38CurrentPort{i}' for i in range(4)]:
 dep=next(r['dependencies']['DiophantineConsistency.'+name] for r in rows if 'DiophantineConsistency.'+name in r['dependencies']);expected=inv['b_only']['DiophantineConsistency/'+name+'.olean'];assert dep['sha256']==expected['sha256'] and dep['realpath']==expected['realpath']
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
t=(q/'src/DiophantineConsistency/Norm38CurrentSeedSource.lean').read_text();assert 'InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)' in t and 'InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)' in t and 'Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3 hz' in t
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_preflight.py')],capture_output=True,text=True,timeout=120);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY',(x.stdout,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'generic_object_sha256':objects[0],'current_object_sha256':objects[1],'author_recorded_session':96515,'author_recorded_exit':0,'guard_slots':sum(len(r['direct_guard']) for r in rows),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Same-witness current seed zero implies shifted symbolic source zero; converse and endpoint open; no Lean replay.'},indent=2,sort_keys=True))
