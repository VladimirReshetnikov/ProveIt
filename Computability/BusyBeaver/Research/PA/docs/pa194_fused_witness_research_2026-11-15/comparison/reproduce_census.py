#!/usr/bin/env python3
"""Memory-bounded read-only census of pinned Git blobs and nested archives.

Recognizes complete five-column numeric TM tables and four JSON encodings:
multiline table strings, arrays of five-field rows, arrays of row strings,
and state/read-keyed dictionaries of three-field actions. It never executes
generators. Git object availability is checked without a promisor fetch.
"""
from pathlib import Path
from collections import Counter
import argparse,csv,gc,hashlib,importlib.util,io,json,re,resource,subprocess,zipfile
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('canonical',HERE/'canonical.py')
canon=importlib.util.module_from_spec(spec);spec.loader.exec_module(canon)

def digest(data):return hashlib.sha256(data).hexdigest()
def parse(data):
 if isinstance(data,bytes):data=data.decode('utf-8')
 rows={};declared=None
 for line in data.splitlines():
  if not line.strip():continue
  if line.lstrip().startswith('#'):
   match=re.search(r'\bstart\s*(\d+)',line)
   if match and declared is None:declared=int(match[1])
   continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  if b not in(0,1)or w not in(0,1)or d not in('L','R')or(q,b)in rows:raise ValueError('invalid row')
  rows[q,b]=(w,d,n)
 states={q for q,b in rows}
 if not states or len(rows)!=2*len(states)or any((q,b)not in rows for q in states for b in(0,1)):raise ValueError('incomplete table')
 if len({n for w,d,n in rows.values()}-states)!=1:raise ValueError('expected one external halt')
 if declared is not None and declared not in states:raise ValueError('bad start')
 start=declared if declared is not None else 0 if states==set(range(len(states)))else None
 return rows,states,start,declared is not None

def table_bytes(rows):return ''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(rows.items())).encode()
def json_tables(obj,path='$'):
 if isinstance(obj,str):
  if '\n'in obj and re.search(r'\b[LR]\b',obj):
   try:yield path,parse(obj)
   except(ValueError,UnicodeError):pass
 elif isinstance(obj,list):
  attempt=None
  if obj and all(isinstance(x,list)and len(x)==5 for x in obj):attempt='\n'.join(' '.join(map(str,x))for x in obj)
  elif obj and all(isinstance(x,str)and len(x.split())==5 for x in obj):attempt='\n'.join(obj)
  if attempt is not None:
   try:yield path,parse(attempt);return
   except(ValueError,UnicodeError):pass
  for i,x in enumerate(obj):
   if isinstance(x,(dict,list,str)):yield from json_tables(x,path+'/'+str(i))
 elif isinstance(obj,dict):
  attempt=[]
  for k,v in obj.items():
   m=re.fullmatch(r'\(?\s*(\d+)\s*[, :/]\s*([01])\s*\)?',k)
   if not m or not isinstance(v,list)or len(v)!=3:break
   attempt.append(' '.join([m[1],m[2],*map(str,v)]))
  else:
   if attempt:
    try:yield path,parse('\n'.join(attempt));return
    except(ValueError,UnicodeError):pass
  for k,v in obj.items():
   if isinstance(v,(dict,list,str)):yield from json_tables(v,path+'/'+k)

def bisimulation(rows,states):
 block={q:0 for q in states}
 while True:
  sig={q:tuple((w,d,block.get(n,-1))for b in(0,1)for w,d,n in[rows[q,b]])for q in states}
  ids={x:i for i,x in enumerate(sorted(set(sig.values())))}
  nxt={q:ids[sig[q]]for q in states}
  if len(set(nxt.values()))==len(set(block.values())):return len(ids)
  block=nxt

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--pin',default='883da8d55452ea097910ed2509a1eefc833ce292');ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 a.output.mkdir(parents=True,exist_ok=True);(a.output/'tables').mkdir(exist_ok=True);(a.output/'nonspanning').mkdir(exist_ok=True)
 git=['git','-c','core.packedGitWindowSize=4m','-c','core.packedGitLimit=16m','-c','core.deltaBaseCacheLimit=16m','-C',str(a.repo)]
 lines=subprocess.check_output(git+['ls-tree','-r','-l',a.pin,'--','Computability/BusyBeaver/Research/PA','docs/incoming'],text=True).splitlines()
 entries=[]
 for line in lines:
  meta,path=line.split('\t',1);mode,typ,h,size=meta.split()
  if typ=='blob'and path.endswith(('.tm','.json','.zip')):entries.append((path,h,int(size)))
 wanted={h for _,h,_ in entries};available=set()
 p=subprocess.Popen(git+['cat-file','--batch-all-objects','--batch-check=%(objectname)'],stdout=subprocess.PIPE,text=True)
 for line in p.stdout:
  h=line.strip()
  if h in wanted:available.add(h)
 if p.wait()!=0:raise RuntimeError('local object inventory failed')
 print('selected',len(entries),'local_blobs',len(available),'wanted_blobs',len(wanted),flush=True)
 occurrences=[];tablemeta={};classes={};payload_cache={};archives={};errors=[];bindings=[];missing=[];counts=Counter()
 norm_cache={}
 def add(loc,item,source_hash,templates,sub):
  rows,states,start,declared=item;data=table_bytes(rows);h=digest(data)
  if h not in tablemeta:
   if h in norm_cache:meta=dict(norm_cache[h])
   else:
    exact=canon.key(rows,states);strong=canon.key(rows,states,True)if len(states)==194 and exact else None
    meta={'states':len(states),'class':exact,'strong_class':strong,'bisimulation_states':bisimulation(rows,states)if len(states)==194 else None}
   meta['normalized_sha256']=h;tablemeta[h]=meta
   cl=meta['class']
   if cl and cl not in classes:
    classes[cl]=dict(meta,first_occurrence=loc)
    if len(states)in(193,194):(a.output/'tables'/(cl+'.tm')).write_bytes(data)
   elif not cl:(a.output/'nonspanning'/(h+'.tm')).write_bytes(data)
  rec={'locator':loc,'normalized_sha256':h,'source_sha256':source_hash,'states':len(states),'start':start,'declared_start':declared,'class':tablemeta[h]['class']}
  occurrences.append(rec);templates.append((sub,h,len(states),start,declared))
 def inspect(data,loc):
  counts['payloads']+=1;h=digest(data)
  if loc.endswith('.zip'):
   counts['archive_references']+=1
   if h in archives:counts['duplicate_archive_references']+=1;return
   archives[h]=loc
   try:
    with zipfile.ZipFile(io.BytesIO(data))as z:
     for n in z.namelist():
      if n.endswith(('.tm','.json','.zip')):inspect(z.read(n),loc+'!'+n)
   except Exception as e:errors.append({'locator':loc,'error':repr(e)})
   return
  if h in payload_cache:
   for sub,nh,ns,start,declared in payload_cache[h]:occurrences.append({'locator':loc+sub,'normalized_sha256':nh,'source_sha256':h,'states':ns,'start':start,'declared_start':declared,'class':tablemeta[nh]['class']})
   return
  found=[]
  if loc.endswith('.tm'):
   try:add(loc,parse(data),h,found,'')
   except Exception as e:errors.append({'locator':loc,'error':repr(e)})
  elif loc.endswith('.json'):
   if b'"L"'not in data and b'"R"'not in data and not re.search(rb'\b[LR]\b',data):payload_cache[h]=[];return
   try:
    obj=json.loads(data)
    for sub,item in json_tables(obj):add(loc+'#'+sub,item,h,found,'#'+sub)
    obj=None
   except Exception as e:errors.append({'locator':loc,'error':repr(e)})
  payload_cache[h]=found
 p=subprocess.Popen(git+['cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for i,(path,h,size)in enumerate(entries):
  if h not in available:missing.append({'path':path,'git_blob':h,'bytes':size});continue
  p.stdin.write((h+'\n').encode());p.stdin.flush();header=p.stdout.readline().decode().split()
  if len(header)!=3 or header[1]!='blob':raise RuntimeError(header)
  data=p.stdout.read(int(header[2]));tail=p.stdout.read(1)
  if len(data)!=size or tail!=b'\n':raise RuntimeError('Git length mismatch')
  hs=hashlib.sha1();hs.update(b'blob '+str(size).encode()+b'\0');hs.update(data)
  if hs.hexdigest()!=h:raise RuntimeError('Git content identity mismatch')
  bindings.append({'path':path,'git_blob':h,'bytes':size,'sha256':digest(data)})
  inspect(data,path);data=None
  if i%100==0:
   gc.collect();print('read',i,'/',len(entries),'normalized',len(tablemeta),'graphs194',sum(c['states']==194 for c in classes.values()),'peak_kib',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
 p.stdin.close();p.wait()
 for name,rows in [('occurrences.csv',occurrences),('source_bindings.csv',bindings)]:
  with(a.output/name).open('w')as f:
   w=csv.DictWriter(f,fieldnames=list(rows[0])if rows else[]);w.writeheader();w.writerows(rows)
 (a.output/'classes.json').write_text(json.dumps(classes,indent=2)+'\n')
 (a.output/'normalized_tables.json').write_text(json.dumps(tablemeta,indent=2)+'\n')
 (a.output/'missing.json').write_text(json.dumps(missing,indent=2)+'\n')
 summary={'pin':a.pin,'tracked_selected_files':len(entries),'missing_tracked_files':len(missing),'occurrences':len(occurrences),'normalized_tables':len(tablemeta),'spanning_classes':len(classes),'spanning_classes_by_states':dict(sorted(Counter(c['states']for c in classes.values()).items())),'nonspanning_normalized_tables':[h for h,c in tablemeta.items()if not c['class']],'archives':archives,'errors':errors,'peak_python_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,**counts}
 (a.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items()if k not in('archives','errors')},indent=2))
 if missing:raise SystemExit('Incomplete input snapshot; missing.json is authoritative')
 if errors:print('Review recognition errors in summary.json',flush=True)
if __name__=='__main__':main()
