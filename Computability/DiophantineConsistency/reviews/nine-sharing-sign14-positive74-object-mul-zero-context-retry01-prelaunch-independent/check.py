#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-positive74-object-mul-zero-context-retry01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='e017fe396668b07d219feb405b3beb06c5665bbfd1806abc181053495d800492' and sha(p/'source-manifest.json')=='6f01e9ed4e8389c59af02bc6cf538b92510d86e4dec67cc4c7efcb88e85fd4a7'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14Positive74ObjectMulZeroContext';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftPartial','DiophantineConsistency.IPRAAddOneDirect'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('compAx mulCore swapArgs, projAx (0 : Fin 2), projAx (1 : Fin 2), mulBaseAx, zeroAx','IPRAEqualityTransGG.ax, reflAx, funAx mulCore (0 : Fin 2), funAx mulCore (1 : Fin 2)','equal (mult a mz) mz','trans (swap a mz) (trans (base a) (unary_zero a))'):assert z in s
old=(root/'research/nine-sharing-sign14-positive74-object-mul-zero-context-check/src/DiophantineConsistency/Sign14Positive74ObjectMulZeroContext.lean').read_text()
needle='  simp [mz, applyCode, vars, equal, IPRANativeEquationSpecialize.equal, Rew.func, Function.comp_def]\n'
assert old.replace(needle,needle+'  constructor\n  · funext i\n    fin_cases i <;> rfl\n  · funext i\n    exact Fin.elim0 i\n')==s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-mul-zero-context-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-positive74-object-shift-partial-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'framework-survey.py')],capture_output=True,text=True,check=True,timeout=180);f=json.loads(x.stdout);assert f['status']=='PASS' and f['observed']['IPRAAddOneDirect']['sha256']=='34016e7d69ee2a8a1c7ed44132ef49b9b9cacf06c4117625c543885d26df32c3'
r=(p/'run.py').read_text();assert "'-M3600'" in r and "LEAN_NUM_THREADS='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed multiplication-zero from explicit finite axiom context; context-to-nativeTheory bridge separate'},indent=2))
