import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent; D=P.parents[1]; R=D/'research'; q=R/'nine-sharing-norm38-seed-static-iff-check'; a=q/'attempt01'; out=Path('/tmp/nine-sharing-norm38-seed-static-iff-check-20261105'); sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='ebc30ad19643e6e0fe5eb5f253163d660c8510165e902d53150e11d75a9be578'
s=json.loads((a/'state.json').read_text()); assert s['status']=='PASS' and len(s['rows'])==1 and s['base_state_sha256']=='ae9f8310391bea63f5d591966b81284846bbf0f526c1da00c8a4225fb56c0b74'
r=s['rows'][0]; n='Norm38SeedStaticIff';assert r['module']==n
src=q/'src/DiophantineConsistency'/f'{n}.lean'; assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']=='4e50939e858e2d8e6f6ad8d5726e993c14a098d070f9002095345cd02e7cc3de'
obj=out/'lib/DiophantineConsistency'/f'{n}.olean'; assert sha(obj)==r['object_sha256']=='b66b343c8806e38f1c247fed3493622102fa2c0f6114cd1d60bb95e0a2fa8af0'
assert sha(q/'run.py')==s['runner_sha256']=='0cf443dd29de95ee7690fbeb757a919c92b7fe2b062e56f02009ad8fa84a1146'
assert sha(q/'source-manifest.json')=='438be22e558c613b101e40b3b1d93c7ba6dba5eb7e4890559fd1bfdc32e9ca1c'
outer=a/'outer-terminal-author-record.json'; assert sha(outer)=='9f4a7896439032d4cec7e0a9c215b5378118e663b24ee875d4ddc5e08f4dab2b'; o=json.loads(outer.read_text());assert o['outer_session_id']==88532 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache: cache[k]=sha(p)
 assert cache[k]==h
for typ in ('deps','compile'):
 z=r[typ]; assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/(n+'-'+typ+'.txt'),z['log_sha256'])
log=(a/(n+'-compile.txt')).read_text();assert '[propext,\n Classical.choice,\n Quot.sound]' in log and 'warning:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else: check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
expected={'Norm38GatesAssembly':'70830fc749e108a9776b1ec8274427e47476d3dbb94916688b0a76a2fc476b09','Norm38FiveNorms':'ea31b12a3933596dc35448c05a91b17dcb3c915ff8ed13c603caf161d136051d','Norm38StaticToSeed':'1e1cbb3ca4feb02070c15c0a70d65e2ae77ec6772cf170620cda45a8d8e00a84'}
for mod,h in expected.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath'])
for name in ('nine-sharing-norm38-gates-assembly-terminal-independent','nine-sharing-norm38-five-norms-v2-terminal-independent','nine-sharing-norm38-static-to-seed-retry01-terminal-independent'):
 p=D/'reviews'/name; x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
t=src.read_text();assert 'InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w) ↔' in t and 'NormAssignment38.gatesHold ι ports w ∧ NormAssignment38.fiveNorms ι ports w' in t
assert '∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)' in t and '[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in t
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':sha(obj),'author_recorded_outer_session':88532,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'direct_producers':expected,'axioms':['propext','Classical.choice','Quot.sound'],'scope':'Retained point checks and producer review replays; no Lean replay or independent observation of historical process.'},indent=2,sort_keys=True))
