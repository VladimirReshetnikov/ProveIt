import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-checkpoint27-34-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint27-34-check-20261106');n='Norm38MacroCheckpoint27to34';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='9cf763c0ddec5fc5505f1b396257b83e20ca6936ada2a11ab25f1666547ddc68';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='983d5bf17bb7f2ec8e9a141e8a7d6a0d0271487701fc0a03c9909bb41a8c8292';assert sha(a/'outer-terminal-author-record.json')=='b99b187574f2fdbd9306ee19d1b2cfa087d7997ada1a279c4d4d768d6af79756';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==48095 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='4693daae8e6c0f64c75480e88fd3d240b1e6862b0af9461ce043a45757790ed0' and r['object_sha256']=='92c83d8b5fbd508a804fabfc51aefb184225bda00a0a349d80374677258aab39'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem path27_34','theorem lookup27_34']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Norm38MacroCheckpoint27to34.path27_34' does not depend on any axioms" in log
assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpoint27to34\.lookup27_34' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpoint27to34\.d34_phi_value' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1227
for mod,h in {'Norm38MacroPath18to45':'e745b03d17c4a9ae99452cacda9d98ad8103d902395e56976ba48a37f382ba21','Norm38MacroLive18Group03':'2589ac6c78d736a31bd3e851aaa0068d43ec0a10a10b3cb648b4df8b7da9d902','Norm38MacroPrefixInputsB':'43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':48095,'author_exit':0,'axiom_reports':'path axiom-free; both lookups [propext, Classical.choice, Quot.sound]','guard_slots':200,'overlay_links':1227,'scope':'Concrete d27 to d34 path and phi value only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
