#!/usr/bin/env python3
"""Fetch and audit all explicit-table-capable PA inputs outside PA/docs.

Uses the exact pinned GitHub trees and checks every retrieved Git blob hash.
This optional online source audit is separate from offline verify_corpus.py.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from collections import Counter,defaultdict
import argparse,hashlib,io,json,urllib.request
import literal_inventory as lit
import json_inventory as js
import machine_classes as mc
PIN='793c68737d94bffa4e32a75bce6cc8058d6d22f0'
PA='Computability/BusyBeaver/Research/PA'
API='https://api.github.com/repos/VladimirReshetnikov/ProveIt/'
RAW='https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'+PIN+'/'
ROOT=Path(__file__).resolve().parent
def get(url):return urllib.request.urlopen(url,timeout=60).read()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT);a=ap.parse_args();out=a.output;out.mkdir(parents=True,exist_ok=True)
 top=json.loads(get(API+'contents/'+PA+'?ref='+PIN));entries=[];trees=[]
 def subtree(r):
  d=json.loads(get(API+'git/trees/'+r['sha']+'?recursive=1'));assert not d.get('truncated');return r,d
 dirs=[r for r in top if r['type']=='dir'and r['name']!='docs']
 with ThreadPoolExecutor(max_workers=6)as pool:
  for r,d in pool.map(subtree,dirs):
   trees.append(dict(path=r['path'],tree_sha=r['sha'],entries=d['tree']))
   entries.extend(dict(path=r['path']+'/'+e['path'],sha=e['sha'])for e in d['tree']if e['type']=='blob')
 entries.extend(dict(path=r['path'],sha=r['sha'])for r in top if r['type']=='file')
 selected=sorted([r for r in entries if Path(r['path']).suffix.lower()in{'.tm','.json','.txt','.csv','.tsv','.zip'}],key=lambda r:r['path'])
 assert len(selected)==126,(len(selected),Counter(Path(r['path']).suffix for r in selected))
 print('Downloading',len(selected),'pinned support blobs',flush=True)
 def payload(r):
  b=get(RAW+r['path']);blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==r['sha'],r['path'];return r,b
 files=[];occ=[];known={}
 def accept(tm,path,pointer=None):
  rows,states,halt=tm;b=''.join(f'{q} {r} {w} {d} {t}\n'for(q,r),(w,d,t)in sorted(rows.items())).encode();h=hashlib.sha256(b).hexdigest();known[h]=b;occ.append(dict(path=path,json_pointer=pointer,normalized_sha256=h,states=len(states)))
 with ThreadPoolExecutor(max_workers=8)as pool:
  for number,(r,b)in enumerate(pool.map(payload,selected)):
   relative='support_inputs/'+r['path'];p=out/relative;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
   files.append(dict(path=r['path'],bytes=len(b),git_blob_sha=r['sha'],sha256=hashlib.sha256(b).hexdigest(),local_payload=relative))
   if r['path'].endswith('.json'):
    stack=[('$',json.loads(b))]
    while stack:
     ptr,node=stack.pop()
     try:tm=js.decode(node)
     except(ValueError,TypeError,KeyError):tm=None
     if tm:
      if len(tm[1])>=2:accept(tm,r['path'],ptr)
     elif isinstance(node,dict):stack.extend((ptr+'/'+str(k),v)for k,v in node.items()if isinstance(v,(dict,list,str)))
     elif isinstance(node,list):stack.extend((ptr+'/'+str(i),v)for i,v in enumerate(node)if isinstance(v,(dict,list,str)))
   else:
    tm=lit.parse_table(b)
    if tm:accept(tm,r['path'])
   if(number+1)%25==0:print('Fetched',number+1,flush=True)
 classes={}
 for h,b in known.items():
  c=mc.classify(b);c['roots']=sorted(c['roots']);classes[c['table']]=c
 all_keys={r['table_class']for r in json.loads((ROOT/'census/classes.json').read_text())}
 import csv
 all_keys.update(r['table_class']for r in csv.DictReader((ROOT/'catalog/MACHINES.tsv').open(),delimiter='\t'))
 assert set(classes)<=all_keys
 assert(len(occ),len(known),len(classes),sum(r['bytes']for r in files))==(14,13,10,1875084)
 result=dict(pin=PIN,selected_files=126,suffix_counts=dict(Counter(Path(r['path']).suffix for r in files)),total_bytes=sum(r['bytes']for r in files),recognized_occurrences=len(occ),normalized_tables=len(known),table_classes=len(classes),new_classes=[],files=files,occurrences=occ,classes=list(classes.values()),errors=[],scope=__doc__)
 (out/'support_scan.json').write_text(json.dumps(result,indent=2)+'\n');(out/'support_trees.json').write_text(json.dumps(dict(root=top,subtrees=trees),indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k not in('files','occurrences','classes')},indent=2),flush=True)
if __name__=='__main__':main()
