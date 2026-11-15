#!/usr/bin/env python3
"""Pinned literal/explicit-JSON census of PA inputs. No semantic claims.
Recognizers adapted from the attributed supplied PA q-radix census.
Classifies only complete physical 193/194-state tables; larger tables are
counted by occurrence and retain official-catalogue comparison separately.
"""
from pathlib import Path
from collections import Counter, defaultdict
from hashlib import sha256, sha1
import csv, gc, io, json, re, subprocess, sys, zipfile
import literal_inventory as lit
import json_inventory as js
import resource
resource.setrlimit(resource.RLIMIT_AS,(700_000_000,700_000_000))
import machine_classes as mc
import stream_json_tables as streaming
REPO=Path(sys.argv[1]).resolve(); REF=sys.argv[2]
OUT=Path(__file__).resolve().parent/'frontier'; OUT.mkdir(exist_ok=True)
(OUT/'tables').mkdir(exist_ok=True)
raw=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-rz',REF,'Computability/BusyBeaver/Research/PA','docs/incoming'])
entries=[]
for line in raw.split(b'\0'):
 if not line: continue
 meta,path=line.split(b'\t',1);mode,kind,oid=meta.split()
 if kind==b'blob': entries.append((path.decode(),oid.decode()))
del raw
known={}; json_cache={}; text_cache={}; occurrences=[]; files=[]; archive_refs=[]; archives=[]; seen_zip=set(); errors=[]
allowed={'.zip','.tm','.txt','.tsv','.csv','.json'}

def normalize(tm):
 rows,states,halt=tm
 txt=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))
 h=sha256(txt.encode()).hexdigest()
 if h not in known:
  known[h]={'states':len(states),'halt':halt}
  if len(states) in (193,194):
   known[h]['data']=tm
   (OUT/'tables'/(h+'.tm')).write_text(txt)
 return h

def add(h,path,fmt,pointer=None,start=None,start_kind='unknown'):
 item={'path':path,'format':fmt,'normalized_sha256':h,'states':known[h]['states'],'start':start,'start_kind':start_kind}
 if pointer is not None: item['json_pointer']=pointer
 occurrences.append(item)

def inspect(data,path):
 if len(data)>2_000_000:print('large',len(data),path,flush=True)
 suf=Path(path).suffix.lower()
 if suf=='.zip': return scan_zip(data,path)
 h=sha256(data).hexdigest();files.append({'path':path,'bytes':len(data),'sha256':h})
 if suf=='.json':
  if h in json_cache:
   for ptr,dig in json_cache[h]:add(dig,path,'json',ptr)
   return
  json_cache[h]=[]
  if not (b'"L"' in data or b'"R"' in data or b' L ' in data or b' R ' in data or b'"table"' in data or b'"transitions"' in data or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',data)):return
  if len(data)>5_000_000:
   def emit_stream(ptr,tm):
    dig=normalize(tm);json_cache[h].append((ptr,dig));add(dig,path,'json',ptr)
   try:streaming.scan(data,emit_stream)
   except Exception as e:errors.append({'path':path,'error':'streaming: '+str(e)})
   return
  try:obj=json.loads(data)
  except Exception as e: errors.append({'path':path,'error':str(e)});return
  stack=[('$',obj)]
  while stack:
   ptr,node=stack.pop()
   try:tm=js.decode(node)
   except (ValueError,TypeError,KeyError):tm=None
   if tm:
    if len(tm[1])<2:continue
    dig=normalize(tm);json_cache[h].append((ptr,dig));add(dig,path,'json',ptr)
   elif isinstance(node,dict):stack.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
   elif isinstance(node,list):stack.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(dict,list,str)))
 elif suf in ('.tm','.txt','.csv','.tsv'):
  if h not in text_cache:
   tm=lit.parse_table(data)
   if tm:
    dig=normalize(tm)
    match=re.search(rb'(?m)^\s*#[^\n]*\bstart\s*(\d+)',data)
    if match: start=int(match.group(1));kind='declared comment'
    elif sorted(tm[1])==list(range(len(tm[1]))):start=0;kind='dense convention; inspect exceptions'
    else: start=None;kind='unspecified native start'
    text_cache[h]=(dig,start,kind)
   else:text_cache[h]=None
  got=text_cache[h]
  if got:add(got[0],path,'text',start=got[1],start_kind=got[2])

def scan_zip(data,path):
 print('zip',path,flush=True)
 h=sha256(data).hexdigest();archive_refs.append({'path':path,'sha256':h})
 if h in seen_zip:return
 seen_zip.add(h)
 try:
  with zipfile.ZipFile(io.BytesIO(data)) as z:
   archives.append({'path':path,'sha256':h,'bytes':len(data),'members':len(z.infolist())})
   for info in z.infolist():
    if not info.is_dir() and Path(info.filename).suffix.lower() in allowed:inspect(z.read(info),path+'!'+info.filename)
 except Exception as e:errors.append({'path':path,'error':str(e)})

selected=[(p,h) for p,h in entries if Path(p).suffix.lower() in allowed]
for i,(p,h) in enumerate(selected):
 if i%100==0:print('scanning',i,'/',len(selected),p,'tables',len(known),flush=True)
 local=REPO/p
 if local.is_file():data=local.read_bytes()
 else:data=subprocess.check_output(['git','-C',str(REPO),'-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=32m','show',REF+':'+p])
 actual=sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 if actual!=h: raise ValueError('source bytes differ from pin: '+p)
 inspect(data,p)
 if i%100==0:gc.collect()
print('scanned all',len(selected),'files; classifying frontier',flush=True)
occ_by=defaultdict(list)
for r in occurrences:occ_by[r['normalized_sha256']].append(r)
class_cache={};identities=[]
for h,item in known.items():
 if item['states'] not in (193,194):continue
 tm=item['data']; rows,states,halt=tm
 least=None; cosmetic=None; rootids={}
 for q in sorted(states):
  c=lit.canonical(tm,q)
  if c is None:continue
  rootids[q]=sha256(repr(c).encode()).hexdigest()
  if least is None or c<least:least=c
  for mirror,compl in ((False,False),(True,False),(False,True),(True,True)):
   v=c if not mirror and not compl else lit.canonical(tm,q,mirror,compl)
   # Terminal action decoration is retained in action_class; cosmetic allows erasure.
   v=tuple(tuple((0,'R',t) if t==-1 else (w,d,t) for w,d,t in pair) for pair in v)
   if cosmetic is None or v<cosmetic:cosmetic=v
 if least is not None:
  action=sha256(repr(least).encode()).hexdigest();cosh=sha256(repr(cosmetic).encode()).hexdigest()
 else:action=None;cosh=None
 # Match official hash definition, which does not preserve designated start.
 official=mc.classify((OUT/'tables'/(h+'.tm')).read_bytes())
 identities.append({'normalized_sha256':h,'states':item['states'],'action_class':action,'cosmetic_class':cosh,'table_class':official['table'],'spanning':least is not None,'spanning_rooted_classes':rootids,'occurrences':occ_by[h]})
 if len(identities)%25==0:print('classified',len(identities),flush=True)
 del item['data']
classes=defaultdict(list)
for r in identities:
 if r['spanning']:classes[r['states'],r['action_class']].append(r)
frontier=[]
for (n,a),rs in sorted(classes.items()):
 frontier.append({'states':n,'action_class':a,'cosmetic_class':rs[0]['cosmetic_class'],'table_class':rs[0]['table_class'],'normalized_sha256s':[r['normalized_sha256'] for r in rs],'occurrences':[o for r in rs for o in r['occurrences']]})
official=list(csv.DictReader((REPO/'Computability/BusyBeaver/Research/PA/docs/MACHINES.tsv').open(),delimiter='\t'))
off194=[r for r in official if r['states']=='194']
found194={r['table_class'] for r in frontier if r['states']==194}
summary={'commit':REF,'tracked_paths':len(entries),'source_payloads_scanned':len(selected),'selected_suffixes':sorted(allowed),'recognized_occurrences':len(occurrences),'text_occurrences':sum(o['format']=='text' for o in occurrences),'json_occurrences':sum(o['format']=='json' for o in occurrences),'recognized_normalized_tables':len(known),'occurrences_by_physical_states':dict(sorted(Counter(o['states'] for o in occurrences).items())),'spanning_frontier_classes':dict(sorted(Counter(c['states'] for c in frontier).items())),'cosmetic_frontier_classes':dict(sorted((n,len({c['cosmetic_class'] for c in frontier if c['states']==n})) for n in (193,194))),'nonspanning_frontier_normalized_tables':[{'normalized_sha256':r['normalized_sha256'],'states':r['states'],'source':r['occurrences'][0]['path']} for r in identities if not r['spanning']],'official_194_classes':len(off194),'official_194_matched':sum(r['table_class'] in found194 for r in off194),'missing_official194':[r for r in off194 if r['table_class'] not in found194],'distinct_zip_payloads':len(archives),'zip_references':len(archive_refs),'errors':errors,'warning':'Counts include rejected, diagnostic, search and reference tables. Start-free action classes are not counts of proven consistency machines; declared or conventional starts retained separately.'}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(OUT/'census.json').write_text(json.dumps({'summary':summary,'files':files,'archives':archives,'archive_refs':archive_refs,'identities':identities,'classes':frontier},indent=2)+'\n')
for n in (193,194):
 data=[c for c in frontier if c['states']==n]
 (OUT/f'frontier{n}.json').write_text(json.dumps(data,indent=2)+'\n')
 with (OUT/f'frontier{n}.csv').open('w',newline='') as f:
  wr=csv.DictWriter(f,fieldnames=['action_class','cosmetic_class','table_class','states','representative','occurrences'])
  wr.writeheader()
  for c in data:wr.writerow({k:c[k] for k in ('action_class','cosmetic_class','table_class','states')}|{'representative':c['occurrences'][0]['path'],'occurrences':len(c['occurrences'])})
print(json.dumps(summary,indent=2),flush=True)
