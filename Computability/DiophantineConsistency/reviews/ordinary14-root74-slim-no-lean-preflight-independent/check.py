#!/usr/bin/env python3
"""Independent no-Lean inspection and synthetic resource-boundary controls."""
from pathlib import Path
import ast,hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-slim-no-lean-preflight';F=A/'inspect.py'
H=lambda b:hashlib.sha256(b).hexdigest()
pins={A/'README.md':'86a0efaf8138c065158755a359195a4cd1897d5b4bb6a03d76ed2f1164785324',F:'262f3c000ee59324c5ed7881660ae527344ff8d0b321d944bb5f9a8adf0fd4d0'}
tail=b"\nIndependent source review: [root74 refusal preflight](../../reviews/ordinary14-root74-slim-no-lean-preflight-independent/README.md).\n"
for p,h in pins.items():
 data=p.read_bytes()
 if p==A/'README.md':
  assert H(data)=='13a86fd9a8cb71b481aea3e94bb7d45d8233ec7338c7a0e17bd5cdd55ef66777'
  assert data.endswith(tail) and H(data[:-len(tail)])==h
 else:assert H(data)==h,(str(p),H(data),h)
tree=ast.parse(F.read_text())
imports=set()
for n in ast.walk(tree):
 if isinstance(n,ast.Import): imports.update(a.name for a in n.names)
 if isinstance(n,ast.ImportFrom): imports.add(n.module)
 if isinstance(n,ast.Call):
  if isinstance(n.func,ast.Name):assert n.func.id not in ('exec','eval','compile','__import__','open')
  if isinstance(n.func,ast.Attribute):
   if ast.unparse(n.func) not in ('platform.system','name.replace'):
    assert n.func.attr not in ('system','popen','run','Popen','fork','spawn','execv','execve','write_text','write_bytes','unlink','rename','replace','mkdir','rmdir','remove','touch')
   if n.func.attr=='open':assert len(n.args)==1 and isinstance(n.args[0],ast.Constant) and n.args[0].value=='rb'
assert imports=={'hashlib','json','os','platform','sys','pathlib'}
text=F.read_text()
assert "sys.exit(1)" in text and "'can_launch':False" in text
assert "['DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.DiscreteOrderedRingFacts']" in text
for h in ('e357624f5ab38852b316b0b492050dbc1ae4c0f90c90fc8cb0481c9061529f65','33cf47041c950f77cd4535d629dcddfa27ff9ea1fcd21cc1af0fb732dd5eb319','b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'):
 assert h in text,h

def run(args):
 p=subprocess.run([sys.executable,'-I','-S','-B',str(F),*args],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=90)
 assert p.returncode==1 and not p.stderr,(args,p.returncode,p.stderr[:300])
 j=json.loads(p.stdout);assert j['status']=='REFUSED_NOT_LAUNCH_READY' and j['can_launch'] is False
 assert len(j['unconditional_blockers'])>=6 and j['collision_check']['names_count']==162
 assert j['constants']=={'disk_free_must_exceed_bytes':5100000000,'host_mem_available_min_bytes':10*1024**3,'session_rss_stop_bytes':4*1024**3,'stage_timeout_seconds':180,'run_timeout_seconds':21600,'monitor_sample_seconds':0.2}
 assert not j['source_mismatches'] and all(x['matches'] for x in j['pins'])
 return j
for args in ([],['--launch']):run(args)
# Monkeypatch only the imported inspector's resource readers in a subprocess;
# its code, source paths, pins, and refusal behavior remain otherwise intact.
wrapper='''import os,sys,types\nfrom pathlib import Path\np=Path(sys.argv[1]).resolve(); free=int(sys.argv[2]); mem=int(sys.argv[3])\nos.statvfs=lambda _:types.SimpleNamespace(f_bavail=free,f_frsize=1)\nold=Path.read_text\ndef fake(self,*a,**k):\n if str(self)=="/proc/meminfo": return "MemAvailable: %d kB\\n" % (mem//1024)\n return old(self,*a,**k)\nPath.read_text=fake\nexec(compile(old(p),str(p),"exec"),{"__file__":str(p),"__name__":"__main__"})\n'''
cases=[(5100000000,10*1024**3,False,True),(5100000001,10*1024**3,True,True),(5100000001,10*1024**3-1024,True,False)]
for free,mem,disk_ok,mem_ok in cases:
 p=subprocess.run([sys.executable,'-I','-S','-B','-c',wrapper,str(F),str(free),str(mem)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=90)
 assert p.returncode==1 and not p.stderr,(p.returncode,p.stderr[:300])
 j=json.loads(p.stdout);assert j['status']=='REFUSED_NOT_LAUNCH_READY' and j['can_launch'] is False
 assert j['disk']['available_bytes']==free and j['disk']['above_floor']==disk_ok
 assert j['host_memory']['available_bytes']==mem and j['host_memory']['at_least_floor']==mem_ok
 assert len(j['unconditional_blockers'])>=6
print(json.dumps({'scope':'independent static no-launch source review and simulated resource-boundary controls; provider survey treated as separately pending','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'real_refusal_modes':['default','--launch'],'synthetic_disk_bytes':[5100000000,5100000001,5100000001],'synthetic_mem_bytes':[x[1] for x in cases],'all_modes_refuse':True,'collision_names_expected':162},sort_keys=True,indent=2))
