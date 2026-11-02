#!/usr/bin/env python3
"""Source-only inventory of missing BusyBeaver/FirstOrder imports in two explicit roots."""
import hashlib,json,os,re,subprocess
from pathlib import Path
roots=[Path('/tmp/compact44-graph-support-join-01/lib'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')]
sources={'BusyBeaver.':Path('Computability/BusyBeaver/Lean'),'FirstOrder.':Path('Logic/FirstOrder/Lean')}
seen=set(); order=[]; frontier={}; issues=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inspect(name):
 rel=Path(name.replace('.','/')+'.olean'); rows=[]
 for root in roots:
  p=root/rel
  rows.append({'path':str(p),'exists':p.is_file(),'lexists':os.path.lexists(p),'realpath':str(p.resolve()),'sha256':sha(p) if p.is_file() else None})
 return rows
def visit(name):
 if name in seen:return
 seen.add(name); states=inspect(name)
 present=next((x for x in states if x['exists']),None)
 if present:frontier[name]=states;return
 source_root=next((v for k,v in sources.items() if name.startswith(k)),None)
 if source_root is None:
  issues.append({'module':name,'kind':'missing_external','states':states});return
 p=source_root/Path(name.replace('.','/')+'.lean')
 if not p.is_file():issues.append({'module':name,'kind':'missing_source','path':str(p)});return
 raw=p.read_bytes(); imports=re.findall(r'^import\s+([\w.]+)',raw.decode(),re.M)
 for dep in imports:visit(dep)
 res=subprocess.run(['git','show','HEAD:'+str(p)],capture_output=True)
 order.append({'module':name,'source':str(p),'sha256':sha(p),'matches_git_head':res.returncode==0 and hashlib.sha256(res.stdout).hexdigest()==sha(p),'imports':imports,'object_slots':states})
for n in ('BusyBeaver.ZFC.ArithmeticMachineGraphPerm252','BusyBeaver.ZFC.ArithmeticMachineStepPerm252'):visit(n)
print(json.dumps({'status':'source-only; not a Lean dependency query or coherent build','roots':[str(x) for x in roots],'candidate_modules':len(order),'ordered_sources':order,'frontier':frontier,'unresolved':issues},indent=2,sort_keys=True))
