import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-checkpoint34-41-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint34-41-check-20261106');n='Norm38MacroCheckpoint34to41';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='68018c156b2ca198eb974d44d0b37e085067b30f33f96edfd78425514e6500b3';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='8fd6c4ae946367a9c195508e3b92798151e85f1a67692cac096b3ead40dc4609';assert sha(a/'outer-terminal-author-record.json')=='56fa740d8574e1b304ea7a117976e65faf60cdafd682d082e66bee1584d2ea69';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==26453 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='aadc8c43e1b31996b95a7f9e9d1f7438cd4cd5b845680b38a8b0132e3396572b' and r['object_sha256']=='985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem path34_41','theorem lookup34_41']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Norm38MacroCheckpoint34to41.path34_41' does not depend on any axioms" in log
assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpoint34to41\.lookup34_41' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpoint34to41\.d41_N_value' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1228
for mod,h in {'Norm38MacroCheckpoint27to34':'92c83d8b5fbd508a804fabfc51aefb184225bda00a0a349d80374677258aab39','Norm38MacroLive18Group01':'b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd','Norm38MacroPrefixQNCarry':'bd2995f482e56f212b821cb5ced4a9f660119720e20a57cb71aeedf9294c194c'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':26453,'author_exit':0,'axiom_reports':'path axiom-free; both lookups [propext, Classical.choice, Quot.sound]','guard_slots':200,'overlay_links':1228,'scope':'Concrete d34 to d41 path and N value only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
