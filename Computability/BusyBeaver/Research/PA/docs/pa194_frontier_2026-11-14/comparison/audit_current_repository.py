#!/usr/bin/env python3
"""Pinned census of literal and explicit-JSON Turing tables in all PA and incoming archives.

The table recognizers are attributed to the ProveIt PA194Q-radix/AX11 research.
This wrapper verifies source Git objects, recursively follows ZIPs, keeps designated
starts separate, and never interprets graph recognition as a consistency theorem.
No source generators, TeX-printed tables, or arbitrary executable encodings are run.
"""
import argparse,collections,concurrent.futures,hashlib,importlib.util,io,json,pathlib,re,subprocess,sys,time,zipfile
PIN='32d0d8b7d93a63ad4106c18cdb29b37927acdad2'
SCANNER=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(SCANNER));import literal_inventory as lit;import json_inventory as ji
import machine_classes as mc

def sha(b):return hashlib.sha256(b).hexdigest()
def classify(item):
 h,txt=item;data=lit.parse_table(txt);rows,states,halt=data
 forms=[];table_ids=[]
 for q in sorted(states):
  c=lit.canonical(data,q)
  if c is not None:forms.append(c);table_ids.append(mc.rooted(rows,states,q)[0])
 if not forms:return h,{'states':len(states),'graph_hash':None,'table_class':None,'cosmetic_hash':None}
 canonical=min(forms);g=sha(repr(canonical).encode());cost=g
 if len(states)==194:
  forms.extend(c for r,b in [(True,False),(False,True),(True,True)] for q in sorted(states) if (c:=lit.canonical(data,q,r,b)) is not None)
  cost=sha(repr(min(forms)).encode())
 return h,{'states':len(states),'graph_hash':g,'table_class':min(table_ids),'cosmetic_hash':cost}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=pathlib.Path,required=True);ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args()
 REPO=args.repo.resolve();OUT=args.output.resolve();OUT.mkdir(parents=True,exist_ok=True)
 started=time.time();occ=[];tables={};files=[];ziprefs=[];seen_zip=set();fragments=[];errors=[]
 def add(data,path,raw,pointer=None):
  rows,states,halt=data
  if pointer and len(states)<2:fragments.append({'path':path,'pointer':pointer});return
  txt=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items())).encode();h=sha(txt)
  m=None if pointer else re.search(rb'(?m)^\s*#.*?\bstart\s*(\d+)',raw)
  start=int(m.group(1)) if m else None
  basis='explicit comment' if m else 'unknown'
  if start is None and pointer is None and '.native.' not in pathlib.Path(path).name and states==set(range(len(states))):start=0;basis='dense-zero convention (not independently specified)'
  rooted=mc.rooted(rows,states,start)[0] if start in states else None
  occ.append({'path':path,'json_pointer':pointer,'states':len(states),'halt':halt,'raw_sha256':sha(raw),'normalized_sha256':h,'designated_start':start,'start_basis':basis,'rooted_sha256':rooted})
  tables.setdefault(h,txt)
 def inspect(raw,path,ext):
  files.append({'path':path,'bytes':len(raw),'sha256':sha(raw)})
  if ext!='.json':
   d=lit.parse_table(raw)
   if d:add(d,path,raw)
   return
  if not (b'"L"' in raw or b'"R"' in raw or b' L ' in raw or b' R ' in raw or b'"table"' in raw or b'"transitions"' in raw or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',raw)):return
  try:j=json.loads(raw)
  except Exception as e:errors.append({'path':path,'error':str(e)});return
  todo=[('$',j)]
  while todo:
   ptr,node=todo.pop();data=ji.decode(node)
   if data:add(data,path,raw,ptr);continue
   if isinstance(node,dict):todo.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
   elif isinstance(node,list):todo.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(dict,list,str)))
 def archive(raw,path,depth=0):
  h=sha(raw);ziprefs.append({'path':path,'sha256':h,'depth':depth,'bytes':len(raw)})
  if h in seen_zip:return
  seen_zip.add(h)
  try:
   with zipfile.ZipFile(io.BytesIO(raw)) as z:
    for m in z.infolist():
     if m.is_dir():continue
     e=pathlib.Path(m.filename).suffix.lower();p=path+'!'+m.filename
     if e=='.zip':archive(z.read(m),p,depth+1)
     elif e in ('.tm','.txt','.tsv','.csv','.json'):inspect(z.read(m),p,e)
  except Exception as e:errors.append({'path':path,'error':str(e)})
 tracked=[]
 rawtree=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-rz',PIN,'Computability/BusyBeaver/Research/PA','docs/incoming'])
 entries=[]
 for entry in rawtree.split(b'\0'):
  if not entry:continue
  meta,name=entry.split(b'\t',1);mode,kind,obj=meta.decode().split()
  if kind=='blob':entries.append((name.decode(),{'sha':obj}))
 for p,x in entries:
  ext=pathlib.Path(p).suffix.lower()
  if ext not in ('.tm','.txt','.tsv','.csv','.json','.zip'):continue
  raw=(REPO/p).read_bytes() if (REPO/p).is_file() else subprocess.check_output(['git','-C',str(REPO),'cat-file','blob',x['sha']]);git=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
  assert git==x['sha'],(p,git,x['sha'])
  tracked.append({'path':p,'git_sha1':git,'sha256':sha(raw),'bytes':len(raw)})
  if ext=='.zip':archive(raw,p)
  else:inspect(raw,p,ext)
 print('scan complete',len(tracked),len(files),len(occ),len(tables),'elapsed',time.time()-started,flush=True)
 identities={}
 with concurrent.futures.ProcessPoolExecutor(max_workers=2) as e:
  for i,(h,c) in enumerate(e.map(classify,tables.items(),chunksize=1)):
   identities[h]=c
   if i%100==0:print('classified',i,'elapsed',time.time()-started,flush=True)
 groups=collections.defaultdict(list)
 for h,c in identities.items():
  if c['graph_hash']:groups[(c['states'],c['graph_hash'])].append(h)
 summary={'snapshot':PIN,'source_tree_entries':len(entries),'tracked_files_verified':len(tracked),'file_payloads_inspected':len(files),'distinct_zip_payloads':len(seen_zip),'zip_references':len(ziprefs),'table_occurrences':len(occ),'normalized_tables':len(tables),'complete_spanning_one_halt_graphs':len(groups),'graph_classes_by_state_count':dict(sorted(collections.Counter(n for n,g in groups).items())),'nonspanning_normalized_tables':sum(c['graph_hash'] is None for c in identities.values()),'excluded_one_state_json_fragments':len(fragments),'errors':errors,'elapsed_seconds':time.time()-started}
 classes=[];od=collections.defaultdict(list)
 for o in occ:od[o['normalized_sha256']].append(o)
 representatives=OUT/'representatives';representatives.mkdir(exist_ok=True)
 for (n,g),hs in groups.items():
  occurrences=[o for h in hs for o in od[h]]
  # no start inference here: representative bytes identify the action graph only.
  def score(o):return (sum(k in o['path'].lower() for k in ['comparison/','reference/','references/','search/','research/','inputs/','census/']),o['json_pointer'] is not None,len(o['path']))
  best=min(occurrences,key=score)
  row={'states':n,'graph_hash':g,'table_class':identities[hs[0]]['table_class'],'cosmetic_hash':identities[hs[0]]['cosmetic_hash'],'normalized_identities':hs,'representative':best,'occurrences':occurrences}
  classes.append(row)
  if 193<=n<=196:(representatives/(g+'.tm')).write_bytes(tables[best['normalized_sha256']])
 result={'scope':__doc__,'summary':summary,'classes':classes,'identities':identities,'occurrences':occ,'tracked_files':tracked,'archive_references':ziprefs,'excluded_fragments':fragments}
 (OUT/'full_census.json').write_text(json.dumps(result,indent=2));(OUT/'full_summary.json').write_text(json.dumps(summary,indent=2))
 (OUT/'frontier194_full.json').write_text(json.dumps([r for r in classes if r['states']==194],indent=2))
 print(json.dumps(summary,indent=2),flush=True)
if __name__=='__main__':main()
