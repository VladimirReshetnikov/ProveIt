#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-function-binary-retry01-check';old=root/'research/nine-sharing-sign14-positive74-object-function-binary-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='b20b12266933c16907557705707c1100caf82df80d0d3d489821236fa301dab1' and sha(p/'source-manifest.json')=='805425c02e46d4b107ac1e71e023faf90a1720c4c68d48e8ef99ec4cfc50179d'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectFunctionBinary';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();a=(old/'src/DiophantineConsistency'/(n+'.lean')).read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectFunctionOpen'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
a=a.replace('    Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rew.func, Function.comp_def]\n','    Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rew.func, Function.comp_def]\n  constructor\n  · constructor <;> funext i <;> fin_cases i <;> simp\n  · funext i\n    fin_cases i <;> simp [Rew.func, Function.comp_def, funext_iff, Fin.forall_fin_two]\n',1).replace('  simpa only [binary_body] using functionOpen f ![a,b,c,d]','  rw [← binary_body f a b c d]\n  exact functionOpen f ![a,b,c,d]',1);assert s==a
for f in ('nine-sharing-sign14-positive74-object-function-binary-failure-independent','nine-sharing-sign14-positive74-object-function-open-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'binary congruence vector-normalization retry; general structural alignment separate'},indent=2))
