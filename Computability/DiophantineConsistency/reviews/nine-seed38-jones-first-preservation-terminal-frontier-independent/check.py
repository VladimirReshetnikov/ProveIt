import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-first-preservation-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-first-preservation-check-20261106');n='Norm38FirstPreservation';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='e788467f452c0afc11b78713e2058ec40ccf79cab84fd19267c5966ac19454c8';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='99b9dfbad984ccce93bb08ed25103b670cdd29d7ff47fea01443153586224379';assert sha(a/'outer-terminal-author-record.json')=='cd3859e8d1b182f0229af12c76c5755fb3e86f8d179a11504ac062eaaa81b944';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==34838 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='e164df6d225df13f13a69be44f52796dbdfb3bc0e3d193c1995ae175259b9de7' and r['object_sha256']=='28f4f5623acd896f94ca7cab4c539fe965536ca0e94c98354aed2a0429d6caf8'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
assert 'theorem d45_first_eq_d1' in t and 'theorem recipe_first_value' in t and 'Norm38MacroRecipe.recipe.values a ⟨0, by decide⟩' in t and t.count('exact Norm38MacroCuts.snoc_previous a')==44
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='9b184b0d2d8df1456df50e35a6ad3093c92da4777aad0d6df7d077db357fc74b' and 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for theorem in ['d45_first_eq_d1','recipe_first_value']:assert f"'DiophantineConsistency.Norm38FirstPreservation.{theorem}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1169
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPrefixFirst'];h='a69ba5536b935e388c616cc6c624ecb8da8aaef052b3350bc09d327dd8272c9a';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':34838,'author_exit':0,'axiom_reports':'two reports [propext, Classical.choice, Quot.sound]','guard_slots':100,'overlay_links':1169,'scope':'Full recipe first entry only; no full semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
