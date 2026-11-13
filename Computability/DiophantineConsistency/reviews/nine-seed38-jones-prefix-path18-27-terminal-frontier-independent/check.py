import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-path18-27-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-path18-27-check-20261106');n='Norm38MacroPath18to27';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='9bc09fddf42b1defce2158e9ee9d78eef1a20617812789bc6794b555493849d2';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='9e03c4294480e64ae865208d494def2f537045d3f650c947643cb5a4057a113d';assert sha(a/'outer-terminal-author-record.json')=='07dae92e11ca3583bc4bf15dce24b9a2a93c088022fffe0542205b89f0eb6122';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==49856 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='efae242aed7e8139a7fe5c4adc67bbc8574fefa2830a02bee7b5cdfccfd3fb18' and r['object_sha256']=='bf606152c9813c75de33752bb7c510814bf97c1cc2a3cb66faf2a6c56c48ee79'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem path18_27','theorem lookup18_27']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Norm38MacroPath18to27.path18_27' does not depend on any axioms" in log
assert re.search(r"'DiophantineConsistency\.Norm38MacroPath18to27\.lookup18_27' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1222
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPath18to20'];h='0a55af76feec76743016a3c845bf21053e3aa52312deb2a98db9229adf745e41';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':49856,'author_exit':0,'axiom_reports':'path axiom-free; lookup [propext, Classical.choice, Quot.sound]','guard_slots':100,'overlay_links':1222,'scope':'Concrete d18 to d27 path and lookup only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
