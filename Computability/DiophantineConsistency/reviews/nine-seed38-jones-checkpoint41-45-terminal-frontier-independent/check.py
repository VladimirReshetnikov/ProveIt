import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-checkpoint41-45-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-checkpoint41-45-check-20261106');n='Norm38MacroCheckpoint41to45';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='78103852f59ba1c747a3e7b709e0a810fd09beca5449c70473cb65e47826789f';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='4fbf346e1ad173a7c25bf3c8c6d7568c4e60406e612c8d96453568c800c708a8';assert sha(a/'outer-terminal-author-record.json')=='87efe58ba5f68165a6c5b0bc86b9bd0747805fd8b79ac8d42851d841aba47a3a';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==24164 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='606c7c153863e98662eadb430b442cc28bebec34e4676446b2066c5b6eedf249' and r['object_sha256']=='d0dc8713317ad6f6b829c3776d740169273d9abecbf5a344489c148fb04cb565'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem path41_45','theorem lookup41_45']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Norm38MacroCheckpoint41to45.path41_45' does not depend on any axioms" in log
assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpoint41to45\.lookup41_45' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpoint41to45\.d41_g_value' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for theorem in ('lookup_recipe41','d41_G_value'):assert re.search(r"'DiophantineConsistency\.Norm38MacroCheckpoint41to45\."+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==300 and len(s['overlay_links'])==1229
for mod,h in {'Norm38MacroCheckpoint34to41':'985b8dc3c317314b6b62d7ed54e1a5b4787b1cf6a9651141fcea8b4020b12155','Norm38MacroLive18Group01':'b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd','Norm38MacroLive18Group02':'f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c','Norm38MacroPrefixGsmall':'dd500df7b9ea630528181ee3e1ac62f955822471a9f3385e0a833c13758dbaf2','Norm38MacroPrefixGlarge':'b685399878adfa8efc0fae22b6f9793c1f74079b4266cfff15d86a6a25e89a06'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':24164,'author_exit':0,'axiom_reports':'path axiom-free; both lookups [propext, Classical.choice, Quot.sound]','guard_slots':300,'overlay_links':1229,'scope':'Concrete d41 to recipe path and g/G values only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
