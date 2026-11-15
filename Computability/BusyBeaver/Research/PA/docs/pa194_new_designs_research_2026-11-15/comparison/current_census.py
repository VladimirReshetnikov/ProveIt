#!/usr/bin/env python3
"""Rebuild the explicit-table census of four exactly pinned incoming ZIPs.

Recognizes complete numeric text tables and explicit JSON encodings, including
nested ZIPs. Does not execute generators or infer source-level correctness.
The historical filed corpus is represented separately by its pinned catalogue.
"""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,hashlib,io,json,re,zipfile,csv
import literal_inventory as lit
import json_inventory as js
import stream_json_tables as streaming
import machine_classes as mc
from rebuild_ledgers import ARCHIVES,PIN
ROOT=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--archive-dir',type=Path,required=True);ap.add_argument('--output',type=Path,default=ROOT/'census');a=ap.parse_args()
 out=a.output;out.mkdir(parents=True,exist_ok=True);reps=out/'representatives';reps.mkdir(exist_ok=True)
 known={};occ=[];files=[];zips=[];ziprefs=[];seen_zip=set();cache={};errors=[]
 allowed={'.zip','.tm','.txt','.tsv','.csv','.json'}
 def normalize(tm):
  rows,states,halt=tm;b=''.join(f'{q} {r} {w} {d} {t}\n'for(q,r),(w,d,t)in sorted(rows.items())).encode();h=sha(b)
  if h not in known:known[h]=dict(states=len(states),halt=halt,data=b,tm=tm)
  return h
 def add(h,path,fmt,pointer=None):
  occ.append(dict(path=path,format=fmt,json_pointer=pointer,normalized_sha256=h,states=known[h]['states']))
 def inspect(b,path):
  ext=Path(path).suffix.lower()
  if ext=='.zip':return scan_zip(b,path)
  h=sha(b);files.append(dict(path=path,bytes=len(b),sha256=h))
  if h in cache:
   for fmt,ptr,dig in cache[h]:add(dig,path,fmt,ptr)
   return
  found=[];cache[h]=found
  def accept(fmt,ptr,tm):
   dig=normalize(tm);found.append((fmt,ptr,dig));add(dig,path,fmt,ptr)
  if ext=='.json':
   if not(b'"L"'in b or b'"R"'in b or b' L 'in b or b' R 'in b or b'"table"'in b or b'"transitions"'in b or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',b)):return
   if len(b)>5_000_000:
    try:streaming.scan(b,lambda ptr,tm:accept('json',ptr,tm))
    except Exception as e:errors.append(dict(path=path,error='streaming: '+str(e)))
    return
   try:obj=json.loads(b)
   except Exception as e:errors.append(dict(path=path,error=str(e)));return
   stack=[('$',obj)]
   while stack:
    ptr,node=stack.pop()
    try:tm=js.decode(node)
    except(ValueError,TypeError,KeyError):tm=None
    if tm:
     if len(tm[1])>=2:accept('json',ptr,tm)
    elif isinstance(node,dict):stack.extend((ptr+'/'+str(k),v)for k,v in node.items()if isinstance(v,(dict,list,str)))
    elif isinstance(node,list):stack.extend((ptr+'/'+str(i),v)for i,v in enumerate(node)if isinstance(v,(dict,list,str)))
  else:
   tm=lit.parse_table(b)
   if tm:accept('text',None,tm)
 def scan_zip(b,path):
  h=sha(b);ziprefs.append(dict(path=path,sha256=h))
  if h in seen_zip:return
  seen_zip.add(h)
  try:
   with zipfile.ZipFile(io.BytesIO(b))as z:
    zips.append(dict(path=path,sha256=h,bytes=len(b),members=len(z.infolist())))
    for member in z.infolist():
     if not member.is_dir()and Path(member.filename).suffix.lower()in allowed:inspect(z.read(member),path+'!'+member.filename)
  except Exception as e:errors.append(dict(path=path,error=str(e)))
 for name,blob in ARCHIVES.items():
  b=(a.archive_dir/name).read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
  print('Scanning',name,flush=True);scan_zip(b,'docs/incoming/'+name)
 print('Classifying',len(known),'normalized tables',flush=True)
 groups={};normal=[]
 occurrences=defaultdict(list)
 for r in occ:occurrences[r['normalized_sha256']].append(r)
 for number,(h,item)in enumerate(known.items()):
  rows,states,halt=item['tm'];by_root=[mc.rooted(rows,states,q)for q in states];maximum=max(n for _,n in by_root);key=min(v for v,n in by_root if n==maximum)
  row=dict(normalized_sha256=h,states=len(states),halt=halt,maximum_reachable=maximum,table_class=key,spanning=maximum==len(states),occurrences=occurrences[h])
  normal.append(row)
  if key not in groups:
   (reps/(key+'.tm')).write_bytes(item['data']);groups[key]=dict(table_class=key,states=len(states),maximum_reachable=maximum,spanning=maximum==len(states),representative='representatives/'+key+'.tm',sha256=h,normalized_sha256s=[],occurrences=[])
  groups[key]['normalized_sha256s'].append(h);groups[key]['occurrences'].extend(occurrences[h])
  if(number+1)%100==0:print('Classified',number+1,flush=True)
 classes=sorted(groups.values(),key=lambda r:r['table_class']);frontier=[r for r in classes if r['states']==194 and r['spanning']]
 filed=list(csv.DictReader((ROOT/'catalog/MACHINES.tsv').open(),delimiter='\t'));keys={r['table_class']for r in filed}
 summary=dict(pin=PIN,top_level_archives=4,payloads_inspected=len(files),zip_references=len(ziprefs),distinct_zip_payloads=len(zips),recognized_occurrences=len(occ),normalized_labeled_tables=len(normal),single_terminal_table_classes=len(classes),spanning194_classes=len(frontier),filed_catalogue_classes=len(keys),union_catalogue_keys=len(keys|set(groups)),errors=errors,scope=__doc__)
 for name,data in [('summary',summary),('files',files),('archives',zips),('archive_refs',ziprefs),('occurrences',occ),('normalized_tables',normal),('classes',classes),('frontier194',frontier)]:
  (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
 with(out/'frontier194.csv').open('w',newline='')as f:
  w=csv.DictWriter(f,fieldnames=['table_class','states','representative','sha256','occurrences']);w.writeheader()
  for r in frontier:w.writerow({k:r[k]for k in('table_class','states','representative','sha256')}|{'occurrences':len(r['occurrences'])})
 assert not errors
 assert(len(occ),len(normal),len(classes),len(frontier),len(keys|set(groups)))==(1757,875,723,520,1137),summary
 print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':main()
