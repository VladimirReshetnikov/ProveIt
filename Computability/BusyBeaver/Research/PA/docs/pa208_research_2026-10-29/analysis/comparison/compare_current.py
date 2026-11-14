from pathlib import Path
from collections import deque
import hashlib,json

def read(p):
 d={}
 for ln in p.read_text().splitlines():
  if not ln.strip() or ln.startswith('#'):continue
  q,b,w,dr,z=ln.split(); d[int(q),int(b)]=(int(w),dr,int(z))
 return d

def canonical(d):
 states={q for q,b in d}; names={0:0}; queue=[0]; rows=[]
 for q in queue:
  for b in (0,1):
   w,dr,z=d[q,b]
   if z not in states: t='H'
   else:
    if z not in names:names[z]=len(names);queue.append(z)
    t=names[z]
   rows.append([names[q],b,w,dr,t])
 assert set(names)==states
 return rows,names

root=Path('upstream'); result={}; canon={}
for package in sorted(root.iterdir()):
 if not package.is_dir() or '208' not in package.name:continue
 sub=next(p for p in package.iterdir() if p.is_dir())
 files=list((sub/'machine').rglob('*.native.tm'))
 if (sub/'alternative').exists():files+=list((sub/'alternative').glob('u208.native.tm'))
 for p in files:
  d=read(p)
  if len(d)!=416:continue
  c,mp=canonical(d); key=f'{package.name}/{p.relative_to(sub)}'
  digest=hashlib.sha256(json.dumps(c,separators=(',',':')).encode()).hexdigest()
  result[key]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'canonical_sha256':digest,'source_path':str(p),'native_to_canonical':mp}
  canon[key]=c
classes={}
for key,value in result.items():classes.setdefault(value['canonical_sha256'],[]).append(key)
print(json.dumps(classes,indent=2))
Path('analysis/comparison/current_comparison.json').write_text(json.dumps({'machines':result,'classes':classes},indent=2)+'\n')
