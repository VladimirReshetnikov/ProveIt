#!/usr/bin/env python3
"""Read common explicit JSON table encodings in all pinned PA files and current nested incoming ZIPs."""
from pathlib import Path
from zipfile import ZipFile
from io import BytesIO
from collections import Counter
import json,hashlib,subprocess,gc,ctypes,sys
trim=ctypes.CDLL(None).malloc_trim
from audit_inventory import rooted,digest,sha,BASE,REPO,PA,PIN
from json_recognizer import decode
cache={}; found=[];errors=[];seen_json={};seen_zips=set();files=0
known={x['class'] for x in json.loads((BASE/'census_all/frontier194.json').read_text()) if x['has_spanning_root']}
def scan(loc,b):
 global files
 files+=1;h=sha(b)
 if h in seen_json:
  seen_json[h].append(loc);return
 seen_json[h]=[loc]
 try: data=json.loads(b)
 except Exception as e: errors.append({'source':loc,'error':str(e)});return
 work=[('$',data)]
 while work:
  pointer,node=work.pop()
  decoded=decode(node)
  if decoded is not None:
   rows,states,halt=decoded
   if len(states)==194:
    normalized=''.join(f'{q} {b} {w} {d} {n}\n' for(q,b),(w,d,n)in sorted(rows.items())).encode();dh=sha(normalized)
    if dh not in cache:
     ts=[rooted(rows,states,q) for q in states]; full=[t for t,n in ts if n==194]
     cache[dh]={'class':digest(min(full)) if full else None,'spanning':bool(full),'normalized_sha256':dh}
    found.append({'source':loc,'pointer':pointer,'json_sha256':h,**cache[dh]})
   continue
  if isinstance(node,dict): work.extend((pointer+'.'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
  elif isinstance(node,list):work.extend((pointer+'['+str(i)+']',v)for i,v in enumerate(node)if isinstance(v,(dict,list,str)))
def archive(loc,b):
 h=sha(b)
 if h in seen_zips:return
 seen_zips.add(h)
 with ZipFile(BytesIO(b)) as z:
  for i in z.infolist():
   if i.filename.endswith('.json'):
    scan(loc+'!'+i.filename,z.read(i));gc.collect();trim(0)
    if files%100==0: print('json_files',files,'tables194',len(found),flush=True)
   elif i.filename.endswith('.zip'):archive(loc+'!'+i.filename,z.read(i))
paths=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','--name-only',PIN,PA],text=True).splitlines()
if '--incoming-only' in sys.argv: paths=[]
for p in paths:
 if p.endswith('.json'):
  scan(p,(REPO/p).read_bytes())
  gc.collect();trim(0)
  if files%1000==0:
   print('json_files',files,'tables194',len(found),flush=True)
   (BASE/'json_checkpoint.json').write_text(json.dumps({'files':files,'found':found,'cache':cache,'seen_json':seen_json,'errors':errors}))
print('tracked done',files,flush=True)
(BASE/'json_tracked_checkpoint.json').write_text(json.dumps({'files':files,'found':found,'cache':cache,'seen_json':seen_json,'errors':errors}))
incoming=BASE/'incoming' if (BASE/'incoming').exists() else REPO/'docs/incoming'
for p in sorted(incoming.glob('*.zip')):
 print('JSON archive',p.name,flush=True);archive('docs/incoming/'+p.name,p.read_bytes());gc.collect();trim(0)
 (BASE/'json_incoming_checkpoint.json').write_text(json.dumps({'files':files,'found':found,'cache':cache,'seen_json':seen_json,'errors':errors}))
new=sorted({x['class']for x in found if x['spanning']and x['class']not in known})
summary={'pin':PIN,'json_occurrences':files,'unique_json_payloads':len(seen_json),'recognized194_occurrences_in_distinct_json_payloads':len(found),'unique_normalized194':len(cache),'spanning194_classes':len({x['class']for x in found if x['spanning']}),'additional_spanning194_classes':new,'parse_errors':errors,'scope':'All tracked PA JSON payloads and every distinct recursively nested current incoming ZIP, using explicit row/array/object/string formats of attributed QN/TDY recognizer. No arbitrary generator evaluated; no prose-only table inferred.'}
(BASE/('json_incoming_summary.json' if '--incoming-only' in sys.argv else 'json_summary.json')).write_text(json.dumps(summary,indent=2)+'\n');(BASE/('json_incoming_occurrences.json' if '--incoming-only' in sys.argv else 'json_occurrences.json')).write_text(json.dumps(found,indent=2)+'\n');(BASE/('json_incoming_payload_sources.json' if '--incoming-only' in sys.argv else 'json_payload_sources.json')).write_text(json.dumps(seen_json,indent=2)+'\n')
print(json.dumps(summary,indent=2),flush=True)
