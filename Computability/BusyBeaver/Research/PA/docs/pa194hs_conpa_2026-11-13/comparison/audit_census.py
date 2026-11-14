#!/usr/bin/env python3
"""Read-only literal-machine census for the pinned PA corpus.
Recognizes complete numeric binary 5-column tables in .tm/.txt/.tsv/.csv;
counts nested ZIP payloads once and records every archive reference.
Graph keys forget state labels and designated start and optionally allow
reflection/global symbol exchange. Tables with no spanning root are retained
but excluded from the graph-class count. No semantic certification is made.
"""
from pathlib import Path
import argparse, collections, hashlib, io, json, re, zipfile

EXTS={'.tm','.txt','.tsv','.csv'}
PAT=re.compile(r'^\s*(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)\s*$')

def digest(b): return hashlib.sha256(b).hexdigest()

def parse(data):
 try: text=data.decode('utf-8-sig')
 except UnicodeDecodeError: return None
 rows={}
 for line in text.splitlines():
  if not line.strip() or line.lstrip().startswith(('#',';','//')): continue
  m=PAT.fullmatch(line)
  if not m: return None
  q,r,w,d,t=m.groups(); key=(int(q),int(r))
  if key in rows:return None
  rows[key]=(int(w),1 if d=='R' else 0,int(t))
 states={q for q,r in rows}
 if not states or len(rows)!=2*len(states) or any((q,b) not in rows for q in states for b in (0,1)): return None
 halts={t for w,d,t in rows.values()}-states
 if len(halts)!=1:return None
 return states,halts.pop(),rows

def canonical(parsed,reflect=False,exchange=False):
 states,halt,rows=parsed;n=len(states);best=None
 # States with no predecessors can only be a spanning root. This common
 # initialization case avoids n equivalent searches, without changing keys.
 pred={q:0 for q in states}
 for w,d,t in rows.values():
  if t in states:pred[t]+=1
 roots=[q for q,v in pred.items() if not v]
 if len(roots)>1:return None
 if not roots:roots=sorted(states)
 for root in roots:
  seen={root:0};queue=[root];out=[]
  for q in queue:
   for bit in (0,1):
    w,d,t=rows[q,bit^int(exchange)]
    if t==halt:dest=n
    else:
     if t not in seen:seen[t]=len(seen);queue.append(t)
     dest=seen[t]
    out.extend((w^int(exchange),d^int(reflect),dest))
  if len(seen)==n:
   key=tuple(out)
   if best is None or key<best:best=key
 return best

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 a.output.mkdir(parents=True,exist_ok=True)
 bases=[a.repo/'Computability/BusyBeaver/Research/PA',a.repo/'docs/incoming']
 forms={};tables=[];ziprefs=[];seen_zip=set();rejected=collections.Counter()
 def content(path,data):
  ext=Path(path).suffix.lower()
  if ext=='.zip':
   h=digest(data);ziprefs.append({'path':path,'sha256':h,'size':len(data),'first_payload':h not in seen_zip})
   if h in seen_zip:return
   seen_zip.add(h)
   try:
    with zipfile.ZipFile(io.BytesIO(data)) as z:
     for info in z.infolist():
      if not info.is_dir() and Path(info.filename).suffix.lower() in EXTS|{'.zip'}:
       content(path+'!/'+info.filename,z.read(info))
   except (zipfile.BadZipFile,RuntimeError) as e: rejected['bad_zip']+=1
   return
  if ext not in EXTS:return
  h=digest(data)
  if h not in forms:
   p=parse(data)
   if p is None:forms[h]=None;rejected['non_table_candidate_files']+=1;return
   n=len(p[0]);base=canonical(p)
   cosm=[]
   if base is not None:
    cosm=[canonical(p,r,e) for r,e in ((False,False),(True,False),(False,True),(True,True))]
   rec={'sha256':h,'states':n,'rows':len(p[2]),'halt':p[1],'size':len(data),'graph_key':None if base is None else digest(json.dumps(base,separators=(',',':')).encode()),'cosmetic_key':None if not cosm else digest(json.dumps(min(cosm),separators=(',',':')).encode()),'paths':[]}
   forms[h]=rec
   if n<=196:
    dest=a.output/'literal_tables';dest.mkdir(exist_ok=True);(dest/(h+'.tm')).write_bytes(data)
  rec=forms[h]
  if rec is None:return
  rec['paths'].append(path);tables.append({'path':path,'sha256':h,'states':rec['states']})
 for base in bases:
  for f in sorted(base.rglob('*')):
   if f.is_file() and f.suffix.lower() in EXTS|{'.zip'}:
    content(f.relative_to(a.repo).as_posix(),f.read_bytes())
 valid=sorted((x for x in forms.values() if x is not None),key=lambda x:(x['states'],x['sha256']))
 summary={'repo_commit':'1e407ae841e4666f932777fad977ba784ebbcfd5','scope':['Computability/BusyBeaver/Research/PA','docs/incoming'],'table_extensions':sorted(EXTS),'recognized_occurrences':len(tables),'byte_forms':len(valid),'graph_classes':len({v['graph_key'] for v in valid if v['graph_key']}),'cosmetic_classes':len({v['cosmetic_key'] for v in valid if v['cosmetic_key']}),'non_spanning_byte_forms':sum(v['graph_key'] is None for v in valid),'zip_references':len(ziprefs),'unique_zip_payloads':len(seen_zip),'rejected':dict(rejected),'by_state':{str(n):{'occurrences':sum(t['states']==n for t in tables),'byte_forms':sum(v['states']==n for v in valid),'graph_classes':len({v['graph_key'] for v in valid if v['states']==n and v['graph_key']})} for n in sorted({v['states'] for v in valid})}}
 for filename,obj in [('summary.json',summary),('tables.json',valid),('occurrences.json',tables),('archives.json',ziprefs)]:
  (a.output/filename).write_text(json.dumps(obj,indent=2)+'\n')
 print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
