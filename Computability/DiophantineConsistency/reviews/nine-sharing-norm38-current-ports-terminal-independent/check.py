import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-ports-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-ports-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38CurrentPorts'
assert sha(a/'state.json')==sha(out/'state.json')=='383bea160c761fa51abd69cfa0f07647e489ed85835d5731ac356744d508ad9d';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38CurrentPorts')" and s['base_state_sha256']=='ebc30ad19643e6e0fe5eb5f253163d660c8510165e902d53150e11d75a9be578'
assert sha(q/'run.py')==s['runner_sha256']=='eeb783c0f2516bf321695948de0cc561e41f2b7130c3e89fae07cd7c14ab3bb1' and "'-M2800'" in (q/'run.py').read_text()
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and 'object_sha256' not in r
assert sha(q/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']=='fa3edbe7b05a7efe82808631f0d6a21800ed7db498af61c5d0d1093f5f31bc0c';assert not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
assert sha(a/'outer-terminal-author-record.json')=='cbe680836a95acd3606cf373af0806caf0a5978f19c9ca912a501473efa4efbf';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==52239 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for phase in ('deps','compile'):
 z=r[phase];assert z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'] and z['rss_limit_bytes']==4*1024**3
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
assert r['deps']['exit']==0 and r['compile']['exit']==1
log=(a/f'{n}-compile.txt').read_text();assert ':42:8: error: (kernel) excessive memory consumption detected' in log and log.count('depends on axioms:')==2 and log.count('DiophantineConsistency.Norm38CurrentPorts.port_casts]')==2
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'CurrentKernelData2011':'95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896','Norm38SeedStaticIff':'b66b343c8806e38f1c247fed3493622102fa2c0f6114cd1d60bb95e0a2fa8af0'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath'])
k=Path('/tmp/current14-standard-fresh-build-20261104');assert sha(k/'state.json')=='f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014';ks=json.loads((k/'state.json').read_text());assert ks['status']=='PASS';rows=[z for z in ks['records'] if z['module']=='DiophantineConsistency.CurrentKernelData2011'];assert len(rows)==1;z=rows[0];assert z['exit']==0 and z['object_sha256']=='95901a4dd31bf84f725829e3903c16dc57f7ad118aa9d201046293ca17047896';check(Path(ks['snapshot'])/'src/DiophantineConsistency/CurrentKernelData2011.lean',z['source_sha256']);check(D/'Lean/DiophantineConsistency/CurrentKernelData2011.lean',z['source_sha256']);check(z['log'],z['log_sha256']);assert len(z['direct_inputs'])==4
for v in z['direct_inputs'].values():check(v['path'],v['sha256'])
comp={path:v for path,v in ks['guarded_companions'].items() if '/CurrentKernelData2011.' in path};assert len(comp)==10
for path,v in comp.items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
p=D/'reviews/nine-sharing-norm38-seed-static-iff-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_FAILURE_EVIDENCE_ONLY','author_recorded_session':52239,'outer_exit':1,'lean_compile_exit':1,'state_sha256':sha(a/'state.json'),'sampled_peak_session_rss_bytes':r['compile']['peak_session_rss_bytes'],'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'kernel_direct_inputs':len(z['direct_inputs']),'kernel_companion_slots':len(comp),'scope':'No Lean replay; axiom reports include failed declaration and do not establish proofs.'},indent=2,sort_keys=True))
