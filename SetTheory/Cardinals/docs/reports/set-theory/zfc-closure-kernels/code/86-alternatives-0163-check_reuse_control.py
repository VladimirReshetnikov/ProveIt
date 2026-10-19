"""Reproduce the same-count positive control's complete local/runtime checks.
This is an ordinary checker, not a claim of an exact-machine Lean theorem.
"""
import pathlib,sys,os,importlib.util,json,time,hashlib
root=pathlib.Path(__file__).resolve().parent;candidate=root/'reuse_control8.tm'
os.environ['ZFC246_BASE']=str(root/'recovered/63');os.environ['ZFC246_TABLE']=str(candidate)
spec=importlib.util.spec_from_file_location('f',root/'recovered/64/experiments/decoder/fold_search246.py');f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
def read(path):
 t={}
 for line in path.read_text().splitlines():
  if line.startswith('#'):continue
  q,b,w,d,s=line.split();t[q,int(b)]=int(w),d,s
 return t
baseline=read(root/'recovered/63/machine/zfc_prefix246_old.tm');assert len(f.T)==492
assert all(f.T[k]==baseline[k] for k in f.P)
t0=time.monotonic();rules=0
for i in range(len(f.CASES)):
 ok,n,e=f.check(f.T,i,1000);assert ok,(i,e);rules+=n
# Independent dense literal startup, checked at the claimed complete endpoint.
q='95';h=0;offset=10000;tape=bytearray(20001);left=right=0
for tick in range(411243):
 assert 0<=h+offset<len(tape)
 w,d,q=f.T[q,tape[h+offset]];tape[h+offset]=w;h+=1 if d=='R'else-1
 left=min(left,h);right=max(right,h)
ones=[j-offset for j,b in enumerate(tape)if b]
reference=json.loads((root/'recovered/63/results/bootstrap.json').read_text())['old_labels']
assert(q,h)==('96',-5);assert ones==reference['all_one_positions']
result=dict(status='PASS',table_sha256=hashlib.sha256(candidate.read_bytes()).hexdigest(),working_states=len(f.T)//2,symbolic_cases=len(f.CASES),symbolic_rules=rules,protected_rows=len(f.P),dense_startup_steps=411243,exit_state=q,head=h,whole_tape_equals_baseline_safe_root=True,one_count=len(ones),head_extent=[left,right],seconds=time.monotonic()-t0)
(root/'reuse_control8.complete_validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
