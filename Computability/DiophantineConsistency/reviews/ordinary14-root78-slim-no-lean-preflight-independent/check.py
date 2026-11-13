from pathlib import Path
import ast,hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-root78-slim-no-lean-preflight'
p=A/'inspect.py'; source=p.read_text(); tree=ast.parse(source)
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
# Check that the frozen inspector itself imports no process-launching facility,
# and has no file-write, shell, exec, eval, fork, spawn or process-run call.
imports=[]; calls=[]
for n in ast.walk(tree):
 if isinstance(n,ast.Import):imports.extend(a.name for a in n.names)
 if isinstance(n,ast.ImportFrom):imports.append(n.module)
 if isinstance(n,ast.Call):
  if isinstance(n.func,ast.Name):calls.append(n.func.id)
  elif isinstance(n.func,ast.Attribute):calls.append(n.func.attr)
assert set(imports)<={'hashlib','json','os','platform','sys','pathlib'}
assert not set(calls)&{'exec','eval','compile','popen','fork','spawn','run','Popen','write','write_text','write_bytes','mkdir','unlink','rename','remove','rmdir'}
assert 'os.system' not in source and 'os.replace' not in source
assert "with p.open('rb')" in source
assert 'sys.exit(1)' in source
assert "'disk_free_must_exceed_bytes':5100000000" in source
assert "'above_floor':free>5100000000" in source
assert "'host_mem_available_min_bytes':10*1024**3" in source
assert "'session_rss_stop_bytes':4*1024**3" in source
# Synthetic resource values exercise the actual inspector with normal read-only
# source/provider inputs. No Lean command or filesystem write is performed.
wrapper='''import io,json,os,pathlib,runpy,sys,types,contextlib
p,free,mem=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
os.statvfs=lambda _p:types.SimpleNamespace(f_bavail=free,f_frsize=1)
original=pathlib.Path.read_text
def read_text(self,*a,**kw):
 if str(self)=="/proc/meminfo":return "MemAvailable: %d kB\\n"%(mem//1024)
 return original(self,*a,**kw)
pathlib.Path.read_text=read_text
buf=io.StringIO()
try:
 with contextlib.redirect_stdout(buf):runpy.run_path(p,run_name="__main__")
 code=0
except SystemExit as e:code=e.code
d=json.loads(buf.getvalue())
print(json.dumps({"exit":code,"status":d["status"],"can_launch":d["can_launch"],"above_floor":d["disk"]["above_floor"],"host_floor":d["host_memory"]["at_least_floor"],"names_count":d["collision_check"]["names_count"],"pin_mismatches":sum(not x["matches"] for x in d["pins"]),"source_mismatches":len(d["source_mismatches"])}))
'''
cases=[]
for free,want in [(5100000000,False),(5100000001,True)]:
 r=subprocess.run([sys.executable,'-I','-S','-B','-c',wrapper,str(p),str(free),str(10*1024**3)],capture_output=True,text=True,timeout=120,check=True)
 x=json.loads(r.stdout); assert not r.stderr
 assert x=={'exit':1,'status':'REFUSED_NOT_LAUNCH_READY','can_launch':False,'above_floor':want,'host_floor':True,'names_count':141,'pin_mismatches':0,'source_mismatches':0}
 cases.append({'synthetic_available_bytes':free,'above_floor':want,'exit':x['exit'],'can_launch':x['can_launch']})
r=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--launch'],capture_output=True,text=True,timeout=120)
x=json.loads(r.stdout);assert r.returncode==1 and not r.stderr and x['can_launch'] is False
print(json.dumps({'author_source_sha256':sha(p),'author_readme_sha256':sha(A/'README.md'),'overlay_inventory_sha256':sha(D/'research/ordinary14-root78-slim-overlay/inventory.json'),'static_no_process_or_write_calls':True,'disk_boundary_and_unconditional_refusal':cases,'launch_argument_exit':r.returncode,'lean_run':False},sort_keys=True,indent=2))
