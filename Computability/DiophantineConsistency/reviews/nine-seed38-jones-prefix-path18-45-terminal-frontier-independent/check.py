import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-path18-45-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-path18-45-check-20261106');n='Norm38MacroPath18to45';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='cbfeac916fd53fafbb6c0b9619171830cce1c44960d8780f11c1a280a9297309';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='349b1d0faf57671dce58890e3ac7decd574080ee37b66a89cd7e55c45ce0af4f';assert sha(a/'outer-terminal-author-record.json')=='1b948986d6b9be33ae02f16d38b24759b1c9e71b997e17f57c274a37bb399bb3';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==67998 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='046e61d86f88b61d713475b1355d3fa9692547a9469928cba09f644d53229c6e' and r['object_sha256']=='e745b03d17c4a9ae99452cacda9d98ad8103d902395e56976ba48a37f382ba21'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem path18_45','theorem lookup18_45']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Norm38MacroPath18to45.path18_45' does not depend on any axioms" in log
assert re.search(r"'DiophantineConsistency\.Norm38MacroPath18to45\.lookup18_45' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
assert re.search(r"'DiophantineConsistency\.Norm38MacroPath18to45\.lookup_recipe18' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1225
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPath18to41'];h='b245318d9c4049b569f3199955d2df27a31cdcfd49a1205ca2f8475801e32fa9';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':67998,'author_exit':0,'axiom_reports':'path axiom-free; both lookups [propext, Classical.choice, Quot.sound]','guard_slots':100,'overlay_links':1225,'scope':'Concrete d18 to d45 path and lookup only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
