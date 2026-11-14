#!/usr/bin/env python3
"""Census complete numeric binary TM tables, including nested ZIP copies.
Canonical form fixes start, labels edges by read/write/direction, and BFS-numbers
controls in read-bit order. A second form additionally identifies L/R reflection.
These are structural classifications, never semantic validity claims.
"""
from pathlib import Path
import argparse,subprocess
import io,zipfile,re,json,hashlib,collections,csv
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args()
PIN='768c2be1a8e4d2fcf8aa3443c7b0f084d145734c'
assert subprocess.check_output(['git','-C',str(args.repo),'rev-parse','HEAD'],text=True).strip()==PIN
BASE=args.output.resolve();BASE.mkdir(parents=True,exist_ok=True)
ROWS=re.compile(r'^\s*(-?\d+)\s+([01])\s+([01])\s+([LR])\s+(-?\d+)\s*(?:#.*)?$')
records=[]; failures=[];archives=[];nested_cache={};byte_cache={}; docs=[]
def digest(b):return hashlib.sha256(b).hexdigest()
def table(data):
 h=digest(data)
 if h in byte_cache:return byte_cache[h]
 try:s=data.decode('utf8')
 except UnicodeDecodeError:return None
 d={};count=0
 for l in s.splitlines():
  l=l.strip()
  if not l or l.startswith(('#',';','//')):continue
  m=ROWS.match(l)
  if not m:return None
  q,a,w,dr,t=m.groups();k=(int(q),int(a));v=(int(w),dr,int(t))
  if k in d:return None
  d[k]=v;count+=1
 if not d:return None
 Q={q for q,a in d};halts={t for w,dr,t in d.values()}-Q
 if count!=2*len(Q) or len(halts)!=1:return None
 # Dense labels use 0; inherited native tables start at 74.
 start=0 if 0 in Q else 74 if 74 in Q else min(Q)
 # Native table may include 0 as a runtime state; detect native halt convention.
 halt=next(iter(halts))
 if halt==254 and 74 in Q and not Q==set(range(len(Q))):start=74
 def canon(reflect=False):
  order=[start];ids={start:0};out=[]
  for q in order:
   for a in [0,1]:
    w,dr,t=d[q,a]
    if t in Q and t not in ids:ids[t]=len(ids);order.append(t)
    out.append((ids[q],a,w,('L' if dr=='R' else 'R') if reflect else dr,ids.get(t,-1)))
  return digest(json.dumps(out,separators=(',',':')).encode()),len(order)
 c,reached=canon();mirror,_=canon(True)
 normalized=''.join(f'{q} {a} {w} {dr} {t}\n' for (q,a),(w,dr,t) in sorted(d.items())).encode()
 ans={'states':len(Q),'rows':count,'start':start,'halt':halt,'reachable_states':reached,'byte_sha256':h,'labeled_sha256':digest(normalized),'rooted_sha256':c,'rooted_reflection_sha256':min(c,mirror)}
 byte_cache[h]=ans
 if len(Q)<=195:
  dest=BASE/'tables_by_hash';dest.mkdir(exist_ok=True);(dest/(h+'.tm')).write_bytes(data)
 return ans

def scan_zip(data,locator,top,depth=0):
 h=digest(data)
 try:z=zipfile.ZipFile(io.BytesIO(data))
 except Exception as e:failures.append({'locator':locator,'error':str(e)});return
 # Cache results as relative locators, so nested references remain counted.
 if h in nested_cache:
  rs,ds=nested_cache[h]
  records.extend(dict(x,archive=top,locator=locator+'!'+x['relative_locator']) for x in rs)
  docs.extend(dict(x,archive=top,locator=locator+'!'+x['relative_locator']) for x in ds)
  return
 before=len(records);before_docs=len(docs)
 for inf in z.infolist():
  n=inf.filename
  if inf.is_dir():continue
  loc=locator+'!'+n
  try:
   if n.lower().endswith('.zip'):
    if depth<24:scan_zip(z.read(inf),loc,top,depth+1)
    else:failures.append({'locator':loc,'error':'nested depth cap'})
   elif n.lower().endswith(('.tm','.txt')) and inf.file_size<2000000:
    b=z.read(inf);t=table(b)
    if t:records.append(dict(t,archive=top,locator=loc,member=n))
    elif 'readme' in Path(n).name.lower():
     dd={'archive':top,'locator':loc,'relative_locator':loc.split('!',1)[1],'text':b.decode('utf8',errors='replace')}
     docs.append(dd)
   elif (n.lower().endswith('.tex') or ('readme' in Path(n).name.lower() and n.lower().endswith('.md'))) and inf.file_size<2000000:
    docs.append({'archive':top,'locator':loc,'relative_locator':loc.split('!',1)[1],'text':z.read(inf).decode('utf8',errors='replace')})
  except Exception as e:failures.append({'locator':loc,'error':str(e)})
 # Cached locators relative to this archive, including nested path.
 rs=[dict(x,relative_locator=x['locator'][len(locator)+1:]) for x in records[before:]]
 ds=[dict(x,relative_locator=x['locator'][len(locator)+1:]) for x in docs[before_docs:]]
 nested_cache[h]=(rs,ds)

for p in sorted((args.repo/'docs/incoming').glob('*.zip')):
 b=p.read_bytes();before=len(records);before_d=len(docs)
 scan_zip(b,p.name,p.name)
 rr=records[before:]
 archives.append({'name':p.name,'size':len(b),'sha256':digest(b),'tables':len(rr),'states':dict(sorted(collections.Counter(x['states'] for x in rr).items())),'distinct_rooted_graphs':len({x['rooted_sha256'] for x in rr}),'documents':len(docs)-before_d})
 print(p.name,len(rr),flush=True)
repo=args.repo/'Computability/BusyBeaver/Research/PA'
if repo.exists():
 for p in repo.rglob('*'):
  if p.is_file() and p.suffix.lower() in ['.tm','.txt'] and p.stat().st_size<2000000:
   t=table(p.read_bytes())
   if t:records.append(dict(t,archive='PA directory',locator=str(p.relative_to(repo)),member=str(p.relative_to(repo))))
summary={'archives':len(archives),'table_occurrences':len(records),'distinct_bytes':len({x['byte_sha256'] for x in records}),'distinct_labeled':len({x['labeled_sha256'] for x in records}),'distinct_rooted':len({x['rooted_sha256'] for x in records}),'distinct_rooted_reflection':len({x['rooted_reflection_sha256'] for x in records}),'counts_by_states':dict(sorted(collections.Counter(x['states'] for x in records).items())),'failures':failures}
(BASE/'census.json').write_text(json.dumps({'summary':summary,'archives':archives,'tables':records},indent=2))
(BASE/'documents.json').write_text(json.dumps(docs,ensure_ascii=False))
with (BASE/'archive_census.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=['name','size','sha256','tables','states','distinct_rooted_graphs','documents']);w.writeheader();w.writerows(archives)
print(json.dumps(summary,indent=2))
