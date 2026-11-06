import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];q=D/'research/nine-sharing-norm38-ipra-endpoint-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-ipra-endpoint-check-20261106');n='Norm38IPRAEndpoint'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='d55d3235bbd3636c7a1f7650b306a9786c2e2f3902bbec176599c8565b396ee5'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8' and len(s['rows'])==1
assert sha(q/'run.py')==s['runner_sha256']=='4633e1a32cf0ba7781591752a6ca787e810e435e1715426b6cbdbc452711514f'
assert sha(a/'outer-observation.json')=='b31fbd87baae758c385c696b8482c92d7365c253841a6a4e2d34eef9eadc4b83';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==40553 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='fe84dc25c6d4bb7c7ebfa06d1ff28d622f607c58dc1a4338214e0a40314a7f0c' and r['object_sha256']=='570952bced71ff043c7fa9f0f84af3e99b8a6fea2f373651f12c01e7e6c72125'
cache={}
def check(p,h,real=None):
 p=Path(p);assert p.is_file(); assert real is None or str(p.resolve())==real
 if str(p.resolve()) not in cache:cache[str(p.resolve())]=sha(p)
 assert cache[str(p.resolve())]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
for x in ['ExecutableJones.expression (SharingSeed38.seed CurrentWindowCarry2011.ports) 0','theorem zero_iff_current','theorem polynomialBridge','theorem native_equivalence','theorem standard_equivalence','theorem standard_translated_equivalence','nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','(Semiformula.lMap embedding sourceSentence)ᴺ','Norm38CurrentCastFreeIff.nine_exists_iff_shifted_source','internalZero_positiveShift']:assert x in t,x
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();reports=re.findall(r"'DiophantineConsistency\.Norm38IPRAEndpoint\.(\w+)' depends on axioms: \[([^]]+)\]",log);expected=['zero_iff_current','polynomialBridge','native_equivalence','standard_equivalence','standard_translated_equivalence'];assert [name for name,_ in reports]==expected and all(re.findall(r'[\w.]+',axs)==['propext','Classical.choice','Quot.sound'] for _,axs in reports);assert not re.search(r'warning:|error:|sorryAx',log)
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
assert len(r['direct_guard'])==250
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
assert len(s['overlay_links'])==1162
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='785a2900255b53c9ef9cf38080e87fec182f2da0643412021a163535af883b5c';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
imports=json.loads((q/'source-manifest.json').read_text())['rows'][0]['imports'];assert len(imports)==4
for mod in imports:
 dep=r['dependencies'][mod];sel=survey['selected'][mod];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_survey.py')],capture_output=True,timeout=120);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='785a2900255b53c9ef9cf38080e87fec182f2da0643412021a163535af883b5c'
subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/nine-sharing-norm38-ipra-endpoint-draft-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_observed_session':40553,'author_observed_exit':0,'axiom_reports':expected,'axioms':['propext','Classical.choice','Quot.sound'],'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Symbolic 9-coordinate iPRA endpoint; no literal exported equation/degree binding or Lean replay. Inherited initial-agreement outer numeric exit unknown.'},indent=2,sort_keys=True))
