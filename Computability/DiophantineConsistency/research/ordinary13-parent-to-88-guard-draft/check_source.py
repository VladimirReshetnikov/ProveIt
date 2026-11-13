from pathlib import Path
import hashlib,json,random,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ParentTo88Guard.lean').read_text()
for t in ('theorem bt_eval','theorem b_eval','theorem guard_of_balance','P72Root.cast_port p 0','P72Root.cast_port p 1','linear_combination h'):assert t in s
for name in ('ordinary13-parent-to-88-ring-client-draft','ordinary13-parent-transport-quotients-draft'):
 r=D/'research'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
rng=random.Random(138814)
for _ in range(3000):
 b,F,alpha,A,t=[rng.randrange(-8,9) for _ in range(5)];q=1+b
 guard=(q-F-alpha)*A-F*q-b*t
 assert guard==q*A-((F+alpha)*A+F*q+b*t)
print(json.dumps({'guard_identity_controls':3000,'lean_run':False,'source_sha256':hashlib.sha256((p/'ParentTo88Guard.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
