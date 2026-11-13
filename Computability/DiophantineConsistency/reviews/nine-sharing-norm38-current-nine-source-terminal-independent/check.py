import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-nine-source-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-nine-source-check-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38CurrentNineSource'
assert sha(a/'state.json')==sha(out/'state.json')=='0849e547567401e7d0a55f8edd07cae8253fd22d8b1d83f05dbb94ab8b40540a';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='20c2e1ba07a2131cee639d2e872498a006ce150d22f72ba0cab7fcec3342a64c'
assert sha(q/'run.py')==s['runner_sha256']=='b4bded366e113048f0c6ce0de339d1f8ae089fcb9e387a8ee6d929e4b204d28a' and sha(q/'source-manifest.json')=='c797b0dfbac3cd9f4e2c6d7624ce1ffa2c682ba437d4c6d9f3c03e2529c28004' and sha(q/'provider_preflight.py')=='d02c5e39e9d0edc2d05c7f309d98e98575c76969a4f1ae4bde94a59242945c54'
assert sha(a/'outer-terminal-author-record.json')=='2b7895b94f43da57a75f4196b81bb6c131a9693d06bb005dd8eab42af1a44d6f';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==82120 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='7f26f285457a49a08896c29ad9f063fa5710e1fb091d999a0222199e198946f8' and r['object_sha256']=='5e984b94a1e43d0f52d59408a35f550da9908a13beae0e184190ad940be9a6d8'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '∃ a : Fin 9 → V' in t and '(ExecutableJones.expression (SharingSeed38.seed CurrentWindowCarry2011.ports) 0).evalRing' in t and '∃ v : Fin 14 → V' in t and 'InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports) v' in t and 'w (Fin.castLE (by decide : 14 ≤ 38) j) + 1' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "current_nine_implies_source' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38CurrentSeedSource':'176750b96fc712e1827066d61958dd164852427587d599d5846aeec4d1207d10','SharingSeed38CurrentJones':'9a4695880ffc229505e7cf46a77fb436cb1e7d41f132690cdeb6eb72f4836e2e'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==h and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_preflight.py')],capture_output=True,text=True,timeout=120);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY',(x.stdout,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':82120,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Current symbolic nine-zero implies source zero only; converse and iPRA endpoint open; no Lean replay.'},indent=2,sort_keys=True))
