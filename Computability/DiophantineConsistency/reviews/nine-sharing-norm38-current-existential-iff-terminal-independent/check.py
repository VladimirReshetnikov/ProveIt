import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-existential-iff-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-existential-iff-check-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38CurrentExistentialIff'
assert sha(a/'state.json')==sha(out/'state.json')=='dcbe82fca2f8c866e301d62281696fed13c33ca9240449b784e8439510674ba9';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='0849e547567401e7d0a55f8edd07cae8253fd22d8b1d83f05dbb94ab8b40540a'
assert sha(q/'run.py')==s['runner_sha256']=='68d090f711b868f95ae03453ecf906db35e9cd97fe4745e5931a33f00c23910b' and sha(q/'source-manifest.json')=='b9900e65c2eae03b53bb7ef354aeea4f35bf82012c797fa0df6d64db8764abc3' and sha(q/'provider_preflight.py')=='f5d157e9d23b4f9c836d7282a601cacb0ae1c7dc9bcd96b92e304361eb963100'
assert sha(a/'outer-terminal-author-record.json')=='f7dc95c6889c3919021ee14efa87701a9d1416adbc9b0e709c819952a3dfd39a';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==5558 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='bdb87b01b717b585fc45578b15cc5a4cf9f84262c1693a2f16b36cea08e9900a' and r['object_sha256']=='ff60f85e32694d66ed4fbbaa83e4b84778bb6655fc90a4bc35e621181dca4786'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert t.count('∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j)')==2 and t.count('∃ u : Fin 14 → V')==2 and t.count('(fun j => u j + 1)')==2 and '∃ w : Fin 38 → V' in t and '∃ a : Fin 9 → V' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert log.count('depends on axioms: [propext,\n Classical.choice,\n Quot.sound]')==2 and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38CurrentSeedSource':'176750b96fc712e1827066d61958dd164852427587d599d5846aeec4d1207d10','Norm38CurrentSourceToSeed':'8963b7bb31156f726981321e3541eb9b122046381e4457393f63d530c78bb6ca','SharingSeed38CurrentJones':'9a4695880ffc229505e7cf46a77fb436cb1e7d41f132690cdeb6eb72f4836e2e'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==h and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_preflight.py')],capture_output=True,text=True,timeout=120);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY',(x.stdout,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':5558,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Both existential equivalences retain universal cast hypotheses and shifted source; no endpoint or Lean replay.'},indent=2,sort_keys=True))
