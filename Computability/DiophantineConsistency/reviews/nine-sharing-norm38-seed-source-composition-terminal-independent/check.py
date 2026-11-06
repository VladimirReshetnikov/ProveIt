import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-seed-source-composition-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-seed-source-composition-check-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38SeedSource'
assert sha(a/'state.json')==sha(out/'state.json')=='9bef14e22cf04c4a9b0810dcd71866c40401a1f49d369e068151dfe2b111ce59';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='fcff412df865174d5bf4c2e553bc98b13c9bcc86a87821522426adab2625165b'
assert sha(q/'run.py')==s['runner_sha256']=='bd45917075bc176a48f102d16ed07436b69b0b9d32f704971f3518349bcbb27e' and sha(q/'source-manifest.json')=='892d560c5e1bf186af737487b41a0f51ba089ac310a16b2be18f3f1f538d7eb3' and sha(q/'provider_preflight.py')=='b1041a5ccd7c32bb35e0cb4f3639de8d40e555dc065f63aef775543b612b9859'
assert sha(a/'outer-terminal-author-record.json')=='9907c5c3ce31917f4f51eeb815908f193b46ba0c78766a281a4ca860ca0d34cb';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==30490 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='dc4b15b6aa835c1b3f55ccbc894b79d3de27c4af7c446f287114fe31d4a153bf' and r['object_sha256']=='e4a4092b123ed7dd0b3c6c2d7e88af9447ca3f1a941ded0dba3f656a1edfd766'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)' in t and 'InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)' in t and 'InternalZero (ObjectCurrentEquation2011.expressionAt p)' in t and 'w (Fin.castLE (by decide : 14 ≤ 38) j) + 1' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "seed_zero_implies_source_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38SeedStaticIff':'b66b343c8806e38f1c247fed3493622102fa2c0f6114cd1d60bb95e0a2fa8af0','Norm38StaticSource':'38875a54e297eb2d94aa897c49251177b4b2f904373f7593d153c2a5ebca0384'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==h and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_preflight.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':30490,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Generic-port seed zero implies shifted source zero under four casts; reverse and endpoint remain open; no Lean replay.'},indent=2,sort_keys=True))
