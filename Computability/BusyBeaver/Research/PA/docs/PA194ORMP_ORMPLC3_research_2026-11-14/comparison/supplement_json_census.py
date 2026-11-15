#!/usr/bin/env python3
"""Supplement the fast scanner: all numeric and explicit Boolean LR matrices.

The Boolean convention is False=L, True=R, as documented by the repository
compiler/support code and the incoming MP receipt. Only complete193/194
matrices with one terminal label are relevant to this supplemental audit.
"""
from pathlib import Path
import argparse,gzip,hashlib,io,json,re,zipfile,time
import schema_parser as sp
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source',type=Path,required=True)
ap.add_argument('--base-census',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args();REPO=args.source.resolve();OUT=args.output.resolve();OUT.mkdir(parents=True,exist_ok=True)
data=json.loads(args.base_census.read_text())
known_norm=set(data['identities']);known_graph={c['action_graph_sha256'] for c in data['classes']}
known_occ={(o['path'],o['json_pointer'],o['normalized_sha256']) for o in data['occurrences']}
entries=json.loads(gzip.decompress((HERE/'scope_manifest.json.gz').read_bytes()))
old_direction=sp.direction;old_normalize=sp.normalize_action
sp.direction=lambda v: isinstance(v,bool) or old_direction(v)
sp.normalize_action=lambda a: (a[0],('R' if a[1] else 'L') if isinstance(a[1],bool) else old_normalize(a)[1],a[2])
cache={};zip_seen=set();extra=[];tables={};all_json=0;inspected=0;started=time.time()
bool_pattern=re.compile(rb'(?:[01]\s*,\s*(?:true|false)\s*,\s*\d+|"(?:direction|move|dir|d)"\s*:\s*(?:true|false))')
def analyze(raw,path):
 global all_json,inspected
 all_json+=1
 if len(raw)<2000:return
 h=hashlib.sha256(raw).hexdigest()
 if h not in cache:
  fast=(b'"L"' in raw or b'"R"' in raw or b' L ' in raw or b' R ' in raw or b'"table"' in raw or b'"transitions"' in raw or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',raw))
  if fast and not bool_pattern.search(raw):cache[h]=[];return
  inspected+=1
  try:obj=json.loads(raw)
  except Exception:cache[h]=[];return
  found=[];todo=[('$',obj)]
  while todo:
   ptr,v=todo.pop();candidate=(isinstance(v,(list,dict)) and len(v)>=193) or isinstance(v,str) and len(v)>=2000
   table=sp.parse_json_node(v) if candidate else None
   if table is not None:
    if len(table[1]) in (193,194):
     norm=sp.normalized(table);key=hashlib.sha256(norm).hexdigest();tables.setdefault(key,table)
     found.append((ptr,key,len(table[1])))
    continue
   if isinstance(v,dict):todo.extend((ptr+'/'+str(k),x)for k,x in v.items()if isinstance(x,(dict,list,str)))
   elif isinstance(v,list):todo.extend((ptr+'/'+str(i),x)for i,x in enumerate(v)if isinstance(x,(dict,list,str)))
  cache[h]=found
 for ptr,key,states in cache[h]:
  if (path,ptr,key)not in known_occ:extra.append({'path':path,'json_pointer':ptr,'raw_sha256':h,'normalized_sha256':key,'states':states,'new_normalized_identity':key not in known_norm})
def archive(raw,path):
 h=hashlib.sha256(raw).hexdigest()
 if h in zip_seen:return
 zip_seen.add(h)
 with zipfile.ZipFile(io.BytesIO(raw))as z:
  for info in z.infolist():
   if info.is_dir():continue
   ext=Path(info.filename).suffix.lower()
   if ext=='.zip':archive(z.read(info),path+'!'+info.filename)
   elif ext=='.json':analyze(z.read(info),path+'!'+info.filename)
for i,e in enumerate(sorted(entries,key=lambda e:e['path'])):
 rel=e['path'];ext=Path(rel).suffix.lower()
 if ext not in ('.json','.zip'):continue
 p=REPO/rel
 raw=p.read_bytes()
 if ext=='.zip':archive(raw,rel)
 else:analyze(raw,rel)
 if i%2000==0:print('Processed',i,'json',all_json,'extra',len(extra),'elapsed',round(time.time()-started,1),flush=True)
identities={}
for key,table in tables.items():
 identities[key]=sp.classify(table)
 if key not in known_norm:(OUT/(key+'.tm')).write_bytes(sp.normalized(table))
newgraph=[(key,v)for key,v in identities.items()if v['action_graph_sha256'] and v['action_graph_sha256']not in known_graph]
summary={'json_payload_occurrences':all_json,'unique_json_payloads_examined_after_expanded_screen':inspected,'additional193_194_occurrences':len(extra),'additional_normalized_identities':len({e['normalized_sha256']for e in extra if e['new_normalized_identity']}),'new_spanning_graphs':[{'normalized_sha256':k,**v}for k,v in newgraph], 'elapsed_seconds':round(time.time()-started,2),'direction_convention':'Boolean False=L and True=R; numeric -1=L and1=R; literalL/R retained','scope':'Supplemental complete193/194 matrices only; no arbitrary generator execution.'}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');(OUT/'occurrences.json').write_text(json.dumps(extra,indent=2)+'\n');(OUT/'identities.json').write_text(json.dumps(identities,indent=2)+'\n')
print(json.dumps(summary,indent=2),flush=True)
