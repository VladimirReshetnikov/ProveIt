import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-path18-20-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-path18-20-check-20261106');n='Norm38MacroPath18to20';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='54b596b0c77261cc96e085494f2c98af540094779cf8e0003f0fdf7de02a5133';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='f559a41fda1266565ad53d0014220720586591f1777ec583fa96d44fced375d2';assert sha(a/'outer-terminal-author-record.json')=='200f9338fbc2d8ee20acbefb3c40d7cde4463fa6f9cd0d5a9f6dcc0a3a6a2ad8';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==3734 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='0d5129bfa5fc3fedc920db2a484fc6ab83f4f364350f936490640d4e95ea7196' and r['object_sha256']=='0a55af76feec76743016a3c845bf21053e3aa52312deb2a98db9229adf745e41'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem path18_20','theorem lookup18_20']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Norm38MacroPath18to20.path18_20' does not depend on any axioms" in log
assert re.search(r"'DiophantineConsistency\.Norm38MacroPath18to20\.lookup18_20' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1221
for mod,h in {'Norm38MacroDependentOutput':'39ae6b92258383e0505623a46c01a5ca71952561593a71090c0685508a7f8f58','Norm38MacroPrefixEmbedding':'a7f4b4f604505643e057e48a3f30ee5aaba9780348ee3edbb4ce3a58b58218be'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':3734,'author_exit':0,'axiom_reports':'path axiom-free; lookup [propext, Classical.choice, Quot.sound]','guard_slots':150,'overlay_links':1221,'scope':'Concrete d18 to d20 path and lookup only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
