#!/usr/bin/env python3
"""Independent literal-table census of pinned PA research and nested incoming ZIPs."""
from pathlib import Path
from zipfile import ZipFile
from io import BytesIO
from collections import defaultdict, Counter
import subprocess, json, hashlib, re, csv, sys, os
BASE=Path(__file__).resolve().parent
REPO=Path(os.environ.get('PA_AUDIT_REPO', str(BASE.parent/'ProveIt')))
PIN='8d31445d858761a8f6150c2e5012adae8895e932'
PA='Computability/BusyBeaver/Research/PA'
sha=lambda b:hashlib.sha256(b).hexdigest()
def parse(b):
 rows={}; declared=None
 for l in b.decode('ascii').splitlines():
  l=l.strip()
  if not l: continue
  if l.startswith('#'):
   m=re.search(r'\bstart\s*(\d+)',l)
   if m and declared is None: declared=int(m[1])
   continue
  q,r,w,d,n=l.split(); q,r,w,n=map(int,(q,r,w,n))
  if r not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,r) in rows: raise ValueError('bad row')
  rows[q,r]=(w,d,n)
 states=set(q for q,r in rows)
 if not states or any((q,r) not in rows for q in states for r in (0,1)): raise ValueError('incomplete rows')
 halts={n for w,d,n in rows.values()}-states
 if len(halts)!=1: raise ValueError('not exactly one terminal')
 start=declared if declared is not None else 0 if states==set(range(len(states))) else None
 if start is not None and start not in states: raise ValueError('start absent')
 return rows,states,start,declared is not None

def rooted(rows,states,start,mirror=0,flip=0,loose=0):
 index={start:0}; order=[start]; out=[]
 for q in order:
  for read in (0,1):
   w,d,n=rows[q,read^flip]
   w^=flip
   if mirror: d='L' if d=='R' else 'R'
   if n in states:
    if n not in index: index[n]=len(index); order.append(n)
    out.append((w,d,index[n]))
   else: out.append((0,'R',-1) if loose else (w,d,-1))
 return tuple(out),len(order)

def digest(t): return sha(json.dumps(t,separators=(',',':')).encode())

def classify(b):
 rows,states,start,declared=parse(b)
 rr=[rooted(rows,states,q) for q in states]
 most=max(n for t,n in rr)
 hashes=[digest(t) for t,n in rr if n==most]
 full=[t for t,n in rr if n==len(states)]
 info={'states':len(states),'start':start,'start_declared':declared,'maximum_reachable':most,'table_class_official':min(hashes),'has_spanning_root':bool(full)}
 if start is not None:
  t,n=rooted(rows,states,start);info.update(rooted_class=digest(t),start_reachable=n)
 else: info.update(rooted_class=None,start_reachable=None)
 if full: info['exact_graph_class']=digest(min(full))
 else: info['exact_graph_class']=None
 if len(states)==194 and full:
  strong=min(rooted(rows,states,q,m,f,1)[0] for m in (0,1) for f in (0,1) for q in states if rooted(rows,states,q)[1]==194)
  info['strong_graph_class']=digest(strong)
 return info

payloads={}; occurrences=[]; rejected=[]; zips={}
def table(loc,b,kind):
 h=sha(b)
 if h not in payloads:
  try: payloads[h]={'sha256':h,**classify(b)}
  except Exception as e: payloads[h]={'sha256':h,'error':str(e)}
 d=payloads[h]
 o={'source':loc,'kind':kind,'sha256':h}
 if 'error' in d: rejected.append({**o,'error':d['error']})
 else: occurrences.append(o)
def archive(loc,b):
 h=sha(b)
 if h in zips: zips[h]['aliases'].append(loc);return
 zips[h]={'sha256':h,'size_bytes':len(b),'aliases':[loc],'members':0}
 with ZipFile(BytesIO(b)) as z:
  zips[h]['members']=len(z.infolist())
  for i in z.infolist():
   if i.is_dir(): continue
   if i.filename.lower().endswith('.tm'): table(loc+'!'+i.filename,z.read(i),'zip_tm')
   elif i.filename.lower().endswith('.zip'): archive(loc+'!'+i.filename,z.read(i))

if __name__=='__main__':
 mode=sys.argv[1] if len(sys.argv)>1 else 'incoming'
 if mode=='all':
  cache=BASE/'census_incoming'/'payloads.json'
  if cache.exists(): payloads.update(json.loads(cache.read_text()))
  paths=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','--name-only',PIN,PA],text=True).splitlines()
  for p in paths:
   if p.endswith('.tm'):
    f=REPO/p
    b=f.read_bytes() if f.exists() else subprocess.check_output(['git','-C',str(REPO),'show',PIN+':'+p])
    table(p,b,'tracked_tm')
  print('tracked complete',len(occurrences),flush=True)
 incoming=BASE/'incoming' if (BASE/'incoming').exists() else REPO/'docs/incoming'
 for p in sorted(incoming.glob('*.zip')):
  print('scanning',p.name,flush=True);archive('docs/incoming/'+p.name,p.read_bytes())
 classes=defaultdict(list)
 for o in occurrences:
  d=payloads[o['sha256']]
  k=d.get('exact_graph_class') or 'nonspanning:'+o['sha256']
  classes[k].append(o)
 frontier=[]
 for k,oo in sorted(classes.items()):
  d=payloads[oo[0]['sha256']]
  if d['states']==194: frontier.append({'class':k,**d,'occurrences':oo})
 summary={'pin':PIN,'mode':mode,'literal_occurrences':len(occurrences),'unique_byte_payloads':len(payloads),'valid_unique_payloads':sum('error' not in d for d in payloads.values()),'rejected_occurrences':len(rejected),'distinct_zip_payloads':len(zips),'zip_references':sum(len(z['aliases']) for z in zips.values()),'spanning_classes_by_state_count':dict(sorted(Counter(payloads[oo[0]['sha256']]['states'] for k,oo in classes.items() if not k.startswith('nonspanning:')).items())),'frontier194_spanning':sum(d['has_spanning_root'] for d in frontier),'frontier194_nonspanning_byte_payloads':sum(not d['has_spanning_root'] for d in frontier),'scope':'All complete five-column .tm payloads in specified tracked files and every distinct recursively nested incoming ZIP. Explicit JSON/prose/generator tables not recognized by this script. Nonspanning tables remain distinct by bytes rather than unsupported graph canonization.'}
 out=BASE/('census_'+mode);out.mkdir(exist_ok=True)
 for name,data in [('summary',summary),('payloads',payloads),('occurrences',occurrences),('zip_payloads',zips),('rejected',rejected),('frontier194',frontier)]: (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps(summary,indent=2),flush=True)
