#!/usr/bin/env python3
"""Exact state-isomorphism test with reflection, symbol exchange and ignored terminal actions.
An invariant histogram is only a rejection filter; every accepted match is verified by
an explicit bijection of all working states and both literal transition rows.
"""
from pathlib import Path
import collections,hashlib,io,json,re,sys,zipfile
from audit_corpus import parse,json_tables
CAND=Path(sys.argv[1]); REPO=Path(sys.argv[2]); OUT=Path(sys.argv[3])
cr,cs,cstart,_=parse(CAND.read_bytes()); n=len(cs)
if cstart is None:cstart=min(cs)

def transform(r,states,reflect,bits):
 out={}
 for q in states:
  for b in (0,1):
   w,d,t=r[q,b^bits]
   out[q,b]=(0,'R',-1) if t not in states else (w^bits,('L' if d=='R' else 'R') if reflect else d,t)
 return out

def colors(r,states):
 c={q:0 for q in states}
 # Stable relational colors in a shared vocabulary independent of numeric labels.
 for k in range(12):
  c={q:hashlib.sha256(repr(tuple((w,d,'H' if t==-1 else c[t],t==q) for w,d,t in (r[q,0],r[q,1]))).encode()).hexdigest() for q in states}
 return c

base=transform(cr,cs,False,False); basec=colors(base,cs); basehist=collections.Counter(basec.values())

def equivalent(r,states):
 if len(states)!=n:return None
 for reflect in (False,True):
  for bits in (False,True):
   rr=transform(r,states,reflect,bits); cc=colors(rr,states)
   if collections.Counter(cc.values())!=basehist:continue
   for q in states:
    if cc[q]!=basec[cstart]:continue
    mapping={cstart:q}; inv={q:cstart}; todo=[cstart];ok=True
    for x in todo:
     y=mapping[x]
     for b in (0,1):
      w,d,t=base[x,b]; ww,dd,tt=rr[y,b]
      if (w,d)!=(ww,dd) or (t==-1)!=(tt==-1):ok=False;break
      if t==-1:continue
      if (t in mapping and mapping[t]!=tt) or (tt in inv and inv[tt]!=t):ok=False;break
      if t not in mapping:mapping[t]=tt;inv[tt]=t;todo.append(t)
     if not ok:break
    if ok and len(mapping)==n:return {'reflection':reflect,'bit_exchange':bits,'mapping':mapping}
 return None

seen_bytes={};zips=set();occ=[];matches=[];other=[];examined=0

def table(data,parsed,path):
 rows,states,start,decl=parsed
 if len(states)!=n:return
 normalized=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items())).encode()
 h=hashlib.sha256(normalized).hexdigest()
 occ.append({'locator':path,'normalized_sha256':h})
 if h not in seen_bytes:
  match=equivalent(rows,states);seen_bytes[h]=match
  if match:matches.append({'locator':path,'normalized_sha256':h,'isomorphism':match})

def inspect(data,path):
 global examined
 examined+=1;ext=Path(path).suffix.lower()
 if ext=='.zip':
  h=hashlib.sha256(data).hexdigest()
  if h in zips:return
  zips.add(h)
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   for e in z.infolist():
    if not e.is_dir() and Path(e.filename).suffix.lower() in ('.tm','.txt','.csv','.tsv','.json','.zip'):
     inspect(z.read(e),path+'::'+e.filename)
 elif ext=='.json':
  try:j=json.loads(data)
  except Exception:return
  for ptr,d,p in json_tables(j):table(d,p,path+'::JSON'+ptr)
 else:
  p=parse(data)
  if p:table(data,p,path)
for root in [REPO/'Computability/BusyBeaver/Research/PA',REPO/'docs/incoming']:
 for p in sorted(root.rglob('*')):
  if p.is_file() and p.suffix.lower() in ('.tm','.txt','.csv','.tsv','.json','.zip'):
   inspect(p.read_bytes(),str(p.relative_to(REPO)))
result={'candidate':str(CAND),'sha256':hashlib.sha256(CAND.read_bytes()).hexdigest(),'states':n,'examined_payloads':examined,'distinct_archive_payloads':len(zips),'table_occurrences_same_size':len(occ),'normalized_tables_same_size':len(seen_bytes),'matches':matches,'scope':'Exact graph-isomorphism comparison under any root, reflection, bit exchange, terminal action suppression. Recognizes literal and explicit JSON tables. Does not execute arbitrary generators.','occurrences':occ}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='occurrences'},indent=2))
