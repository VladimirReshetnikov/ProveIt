from pathlib import Path
from hashlib import sha256
import ast,json,re,os,tempfile,subprocess,sys
h=Path('research/trace75-fresh-provider-rebuild');runner=h/'run-v2.py';outer=h/'run-outer.py'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(runner)=='9aaffde57346464f11a963ff4960592c871cd88c3eef8badd5652f6515fca67b';assert sha(outer)=='0ed48c144b4cccc026bd4967d1e410889f8379a522999f66bcf21279aff06d1d'
pre=h/'observations/preflight-attempt02';x=json.loads((pre/'terminal.json').read_text());assert x['exit']==0 and x['runner_sha256_before']==x['runner_sha256_after']==sha(runner) and sha(pre/'stdout')==x['stdout_sha256'] and sha(pre/'stderr')==x['stderr_sha256'] and not (pre/'stderr').read_text();q=json.loads((pre/'stdout').read_text());assert q=={'status':'PREFLIGHT_PASS','base':1931,'outside':80,'supplements':40,'stages':14,'scanner_sha256':sha(runner)}
policy=h/'observations/policy-attempt01/result.json';j=json.loads(policy.read_text());assert j['status']=='PASS' and len(j['checks'])==14 and all(j['checks'].values()) and j['runner_sha256']==sha(runner) and j['test_sha256']==sha(h/'test-policy.py')
plan=json.loads(Path('research/trace75-fresh-provider-plan/observations/plan-attempt01/result.json').read_text());assert len(plan['stage_order'])==14
for n in plan['stage_order']:
 row=plan['producers'][n];receipt=json.loads(Path(row['receipt']).read_text());p=Path(row['receipt']).parent;assert sha(row['receipt'])==row['receipt_sha256'] and sha(row['source'])==sha(p/'source.txt')==row['source_sha256'] and sha(p/'stdout')==receipt['stdout_sha256'] and sha(p/'stderr')==receipt['stderr_sha256'] and not (p/'stderr').read_text()
 expected=re.findall(r'^#print axioms\s+(\S+)',Path(row['source']).read_text(),re.M);assert len(expected)==1
 assert (p/'stdout').read_text()==f"'{expected[0]}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
# Exercise the real supervisor in isolation with deliberately altered runner bytes; no child may run.
with tempfile.TemporaryDirectory(prefix='trace75-outer-pin-review-') as td:
 d=Path(td);(d/'run-outer.py').write_bytes(outer.read_bytes());(d/'run-v2.py').write_text('raise RuntimeError("SHOULD NOT EXECUTE")\n');r=subprocess.run([sys.executable,'-I','-S','-B',str(d/'run-outer.py'),'--attempt','attempt99'],capture_output=True,text=True)
 assert r.returncode!=0 and 'input drift' in r.stderr and not (d/'observations/outer-attempt99').exists() and not (d/'observations/attempt99').exists()
print('PASS: reviewed runner and supervisor hashes, retained preflight and all 14 AST-based controls, exact named stage reports/source snapshots; altered runner rejected by copied actual supervisor before any child launch.')
print('Static review only; no Lean replay or new union launched.')
