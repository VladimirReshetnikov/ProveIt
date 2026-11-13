from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ModelMap87To86.lean').read_text()
for t in ('PowerRecovery87Draft.power','Divides3X87Draft.divides_three_X','MersenneGuard87Draft.strict_of_power','GuardGap87Draft.gap_of_87_zero','ConditionalMap87To86Draft.positive_map','hbeta46 : 46≤beta','hradix : beta=Exp.exp t-1'):assert t in s
for name in ('ordinary14-87-power-recovery-draft','ordinary14-87-mersenne-guard-draft','ordinary14-87-to-86-conditional-map-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'source composition and transitive draft receipt replay, no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'ModelMap87To86.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
