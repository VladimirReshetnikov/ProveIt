import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-static-carrier-retry02';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-static-carrier-retry02-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38StaticCarrierConditional'
assert sha(a/'state.json')==sha(out/'state.json')=='77cba4b06bb6921bccb517e135d94b5b54dc0d25f602774b9d23be9d15c28951';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='7bd683c7d990981e7b1172c16c73c294a4da4f88382949da0d88158c5c580fbc'
assert sha(q/'run.py')==s['runner_sha256']=='8f88b405f71eb6774452e419fd56e1250b03360dcad6231bcc8258c9a972c1c6' and sha(q/'source-manifest.json')=='377a9566c2fa5ffc02611250792cb3fc51ad7e78207645d4965ff7b8662648bb' and sha(q/'field_preflight.py')=='4874dede3ed41c8502933a6b2b9a4303557ea203ef13a58a52f18888235e32f4'
assert sha(a/'outer-terminal-author-record.json')=='633976ef631400bb8c535992f3198899d5d529929894e561948492b78760a4cc';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==89237 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='e6a802d24f38d6eec6193b96ff815b9845465e7f2049aab48d71ff14aa70a011' and r['object_sha256']=='7d0b8cbb7cd6a01447ff710deb1f22336c3765bc4e7b5149b9cc3424eef491f6'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
for idx in (61,44,78,66,80,36):assert f'pairValue ι (v {idx}) = ref {idx}' in t
assert '(hn : NormAssignment38.fiveNorms ι ports w)' in t and 'Carrier65.value (fun j => ι (ports j))' in t and '[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "static_terminals_norms_imply_value' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
dep=r['dependencies']['DiophantineConsistency.Norm38ReferenceFieldsAll'];assert dep['sha256']=='3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd';check(dep['path'],dep['sha256'],dep['realpath'])
p=D/'reviews/nine-sharing-norm38-reference-fields-combine-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':89237,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Six-terminal agreement and five norms remain hypotheses; no Lean replay or unconditional bridge.'},indent=2,sort_keys=True))
