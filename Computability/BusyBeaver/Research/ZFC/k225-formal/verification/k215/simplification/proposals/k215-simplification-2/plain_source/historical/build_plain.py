#!/usr/bin/env python3
"""Serial isolated build, never launching concurrent Lean processes."""
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path('/dev/shm/zfc_proof_audit/plain');directory=root/'BusyBeaver/ZFC'
targets=sys.argv[1:] or ['KSource215']
seen=set();order=[]
def visit(name):
 if name in seen:return
 seen.add(name)
 for line in (directory/(name+'.lean')).read_text().splitlines():
  if line.startswith('import BusyBeaver.ZFC.'):
   visit(line.removeprefix('import BusyBeaver.ZFC.').strip())
 order.append(name)
for t in targets:visit(t)
(root/'build_plan.json').write_text(json.dumps(order,indent=2)+'\n')
for name in order:
 source=directory/(name+'.lean')
 obj=source.with_suffix('.olean'); old=root/'build_logs'/(name+'.json')
 direct=[]
 for line in source.read_text().splitlines():
  if line.startswith('import BusyBeaver.ZFC.'):
   direct.append(directory/(line.removeprefix('import BusyBeaver.ZFC.').strip()+'.olean'))
 if old.exists() and obj.exists():
  data=json.loads(old.read_text())
  if data.get('status')=='PASS' and data.get('source_sha256')==hashlib.sha256(source.read_bytes()).hexdigest() and data.get('object_sha256')==hashlib.sha256(obj.read_bytes()).hexdigest() and all(dep.exists() and dep.stat().st_mtime <= obj.stat().st_mtime for dep in direct):
   print(name,'REUSE unchanged source/object and older direct dependencies',flush=True)
   continue
 command=['python3','/dev/shm/zfc_proof_audit/run_lean.py',str(source),'--root',str(root),'--logs',str(root/'build_logs'),'--timeout','600']
 run=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 record=root/'build_logs'/(name+'.json')
 if record.exists():
  item=json.loads(record.read_text());print(name,item['status'],round(item['seconds'],3),'s',flush=True)
 if run.returncode:
  print(run.stdout.decode(errors='replace'),flush=True);raise SystemExit(run.returncode)
print('ALL REQUESTED MODULES PASS',flush=True)
