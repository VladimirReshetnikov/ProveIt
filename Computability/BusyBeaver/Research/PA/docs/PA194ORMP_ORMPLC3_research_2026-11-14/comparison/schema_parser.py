#!/usr/bin/env python3
"""Read-only table census, with designated starts distinguished from action-graph identity.

Recognizes numeric five-column complete binary tables and explicit JSON equivalents.
Recurses through nested ZIPs, deduplicating byte-identical ZIP payloads. No generators,
Lean definitions, TeX tables or arbitrary executable encodings are evaluated. A table
census is not an assertion of Con(PA) calibration. Reflections preserve blank zero;
symbol complementation is deliberately not used as a blank-start equivalence.
"""
from __future__ import annotations
import argparse, collections, hashlib, io, json, pathlib, re, time, zipfile

EXTENSIONS={'.tm','.txt','.json','.csv','.tsv','.zip'}
def sha(raw):return hashlib.sha256(raw).hexdigest()
def integer(v):return isinstance(v,int) and not isinstance(v,bool) and v>=0
def direction(v):return v in ('L','R',-1,1) and not isinstance(v,bool)
def bit(v):return isinstance(v,int) and not isinstance(v,bool) and v in (0,1)
def normalize_action(a):
 w,d,t=a
 return w,('L' if d==-1 else 'R' if d==1 else d),t

def validate(rows):
 if not rows:return None
 states={q for q,b in rows}
 if len(rows)!=2*len(states) or any((q,b) not in rows for q in states for b in (0,1)):return None
 halts={t for w,d,t in rows.values()}-states
 if len(halts)!=1:return None
 return rows,states,next(iter(halts))

def parse_text(raw):
 try:txt=raw.decode('utf-8') if isinstance(raw,bytes) else raw
 except UnicodeError:return None
 rows={}
 for l in txt.splitlines():
  l=l.strip()
  if not l or l.startswith(('#','//',';')):continue
  a=l.split()
  if len(a)!=5 or not a[0].isdigit() or a[1] not in ('0','1') or a[2] not in ('0','1') or a[3] not in ('L','R') or not a[4].isdigit():return None
  q,b,w,d,t=int(a[0]),int(a[1]),int(a[2]),a[3],int(a[4])
  if (q,b) in rows:return None
  rows[q,b]=w,d,t
 return validate(rows)

def action(v):return isinstance(v,list) and len(v)==3 and bit(v[0]) and direction(v[1]) and integer(v[2])
def record(v):
 if not isinstance(v,dict):return None
 def get(*keys):
  for k in keys:
   if k in v:return v[k]
 q=get('state','source','q','current_state','from');b=get('read','symbol','read_bit','read_symbol','b')
 w=get('write','write_bit','write_symbol','w');d=get('direction','move','dir','d');t=get('next','target','next_state','to','t')
 return (q,b,w,d,t) if integer(q) and bit(b) and bit(w) and direction(d) and integer(t) else None

def parse_json_node(v):
 if isinstance(v,str):return parse_text(v) if '\n' in v else None
 rows={}
 if isinstance(v,list) and len(v)>=2:
  if all(isinstance(x,list) and len(x)==5 and integer(x[0]) and bit(x[1]) and bit(x[2]) and direction(x[3]) and integer(x[4]) for x in v):
   for q,b,w,d,t in v:
    if (q,b) in rows:return None
    rows[q,b]=normalize_action((w,d,t))
  elif all(isinstance(x,list) and len(x)==2 and all(action(a) for a in x) for x in v):rows={(q,b):normalize_action(a) for q,pair in enumerate(v) for b,a in enumerate(pair)}
  elif len(v)%2==0 and all(action(a) for a in v):rows={(i//2,i%2):normalize_action(a) for i,a in enumerate(v)}
  elif all(record(x) is not None for x in v):
   for q,b,w,d,t in map(record,v):
    if (q,b) in rows:return None
    rows[q,b]=normalize_action((w,d,t))
 elif isinstance(v,dict) and v:
  if all(isinstance(k,str) and k.isdigit() and isinstance(x,list) and len(x)==2 and all(action(a) for a in x) for k,x in v.items()):rows={(int(q),b):normalize_action(a) for q,pair in v.items() for b,a in enumerate(pair)}
  elif all(isinstance(k,str) and re.fullmatch(r'\(?\s*\d+\s*[,;:]\s*[01]\s*\)?',k) and action(a) for k,a in v.items()):
   for k,a in v.items():
    q,b=map(int,re.findall(r'\d+',k));rows[q,b]=normalize_action(a)
 return validate(rows)

def canonical(data,root,reflect=False,ignore_final_action=False):
 rows,states,halt=data
 assert root in states
 ren={root:0};order=[root];out=[]
 for q in order:
  for b in (0,1):
   w,d,t=rows[q,b]
   if reflect:d='L' if d=='R' else 'R'
   if t==halt:
    t=-1
    if ignore_final_action:w,d=0,'R'
   else:
    if t not in ren:ren[t]=len(ren);order.append(t)
    t=ren[t]
   out.append((w,d,t))
 return tuple(out),len(order)

def canonhash(c):return sha(json.dumps(c,separators=(',',':')).encode())
def normalized(data):return ''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(data[0].items())).encode()

def classify(data):
 rows,states,halt=data
 forms=[(q,*canonical(data,q)) for q in sorted(states)]
 spanning=[(q,c) for q,c,n in forms if n==len(states)]
 info={'states':len(states),'halt':halt,'spanning_roots':[q for q,c in spanning]}
 if spanning:
  exact=min(c for q,c in spanning)
  mirrored=min([exact]+[canonical(data,q,True)[0] for q,c in spanning])
  halting=min([canonical(data,q,r,True)[0] for q,c in spanning for r in (False,True)])
  info.update(action_graph_sha256=canonhash(exact),reflection_graph_sha256=canonhash(mirrored),halting_graph_sha256=canonhash(halting))
 else:info.update(action_graph_sha256=None,reflection_graph_sha256=None,halting_graph_sha256=None)
 return info

def scan(root,out,manifest=None):
 starttime=time.time();occ=[];payloads=[];archives=[];errors=[];ignored_json=[];tables={};zip_seen=set();direct=[]
 if manifest:
  entries=json.loads(pathlib.Path(manifest).read_text())
  if isinstance(entries,dict):entries=entries.get('tree',entries.get('files',entries.get('entries',[])))
  paths=[(x['path'],x.get('sha') or x.get('git_sha1')) for x in entries if x.get('type','blob')=='blob' and (x['path'].startswith('Computability/BusyBeaver/Research/PA/') or x['path'].startswith('docs/incoming/'))]
 else:
  paths=[(str(p.relative_to(root)),None) for prefix in ('Computability/BusyBeaver/Research/PA','docs/incoming') for p in (root/prefix).rglob('*') if p.is_file()]
 def add(data,raw,path,ptr=None):
  rows,states,halt=data
  if ptr is not None and len(states)<2:ignored_json.append({'path':path,'pointer':ptr});return
  norm=normalized(data);h=sha(norm);tables.setdefault(h,data)
  m=None if ptr else re.search(rb'(?mi)^\s*(?:#|//|;).*?\bstart\s*(\d+)',raw)
  start=int(m.group(1)) if m else None;basis='explicit comment' if m else 'unknown'
  if start is None and ptr is None and '.native.' not in pathlib.Path(path).name.lower() and states==set(range(len(states))):start=0;basis='dense-zero convention; inspect README for authority'
  rooted=None;reach=None;mirrored=None
  if start in states:
   c,reach=canonical(data,start);rooted=canonhash(c);mirrored=canonhash(min(c,canonical(data,start,True)[0]))
  elif start is not None:errors.append({'path':path,'error':'declared start not a working state'})
  occ.append({'path':path,'json_pointer':ptr,'states':len(states),'raw_sha256':sha(raw),'normalized_sha256':h,'designated_start':start,'start_basis':basis,'reachable_from_designated_start':reach,'rooted_sha256':rooted,'rooted_reflection_sha256':mirrored})
 def inspect(raw,path,ext):
  payloads.append({'path':path,'bytes':len(raw),'sha256':sha(raw)})
  if ext!='.json':
   d=parse_text(raw)
   if d:add(d,raw,path)
   return
  if not (b'"L"' in raw or b'"R"' in raw or b' L ' in raw or b' R ' in raw or b'"table"' in raw or b'"transitions"' in raw or re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,',raw)):return
  try:j=json.loads(raw)
  except Exception as e:errors.append({'path':path,'error':'JSON: '+str(e)});return
  todo=[('$',j)]
  while todo:
   ptr,node=todo.pop();d=parse_json_node(node)
   if d:add(d,raw,path,ptr);continue
   if isinstance(node,dict):todo.extend((ptr+'/'+str(k),v) for k,v in node.items() if isinstance(v,(dict,list,str)))
   elif isinstance(node,list):todo.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(dict,list,str)))
 def archive(raw,path,depth=0):
  h=sha(raw);archives.append({'path':path,'sha256':h,'bytes':len(raw),'depth':depth})
  if h in zip_seen:return
  zip_seen.add(h)
  try:
   with zipfile.ZipFile(io.BytesIO(raw)) as z:
    for m in z.infolist():
     if m.is_dir():continue
     ext=pathlib.Path(m.filename).suffix.lower()
     if ext=='.zip':archive(z.read(m),path+'!'+m.filename,depth+1)
     elif ext in EXTENSIONS:inspect(z.read(m),path+'!'+m.filename,ext)
  except Exception as e:errors.append({'path':path,'error':'ZIP: '+str(e)})
 for p,gitsha in sorted(paths):
  ext=pathlib.Path(p).suffix.lower()
  if ext not in EXTENSIONS:continue
  f=root/p
  if not f.is_file():errors.append({'path':p,'error':'missing file'});continue
  raw=f.read_bytes();got=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
  if gitsha is not None and got!=gitsha:errors.append({'path':p,'error':'Git blob mismatch','expected':gitsha,'actual':got});continue
  direct.append({'path':p,'git_sha1':got,'bytes':len(raw),'sha256':sha(raw),'verified_against_manifest':gitsha is not None})
  if ext=='.zip':archive(raw,p)
  else:inspect(raw,p,ext)
 print('Recognized',len(occ),'occurrences',len(tables),'normalized tables',flush=True)
 identities={}
 for i,(h,data) in enumerate(tables.items()):
  identities[h]=classify(data)
  if i%100==0:print('Classified',i,'elapsed',round(time.time()-starttime,2),flush=True)
 groups=collections.defaultdict(list)
 for h,c in identities.items():
  if c['action_graph_sha256']:groups[(c['states'],c['action_graph_sha256'])].append(h)
 bynorm=collections.defaultdict(list)
 for o in occ:bynorm[o['normalized_sha256']].append(o)
 classes=[];repdir=out/'representatives';repdir.mkdir(parents=True,exist_ok=True)
 for (n,g),hs in sorted(groups.items()):
  oo=[o for h in hs for o in bynorm[h]]
  def rank(o):return (sum(t in o['path'].lower() for t in ('research/','search/','reference/','references/','comparison/','inputs/','census/')),o['designated_start'] is None,len(o['path']),o['path'])
  best=min(oo,key=rank)
  classes.append({'states':n,'action_graph_sha256':g,'reflection_graph_sha256':identities[hs[0]]['reflection_graph_sha256'],'halting_graph_sha256':identities[hs[0]]['halting_graph_sha256'],'representative':best,'normalized_tables':hs,'occurrences':oo})
  if 193<=n<=196:(repdir/(g+'.tm')).write_bytes(normalized(tables[best['normalized_sha256']]))
 summary={'direct_payloads':len(direct),'direct_git_blobs_verified':sum(x['verified_against_manifest'] for x in direct),'inspected_payloads':len(payloads),'distinct_zip_payloads':len(zip_seen),'zip_references':len(archives),'table_occurrences':len(occ),'normalized_tables':len(tables),'spanning_action_graph_classes':len(classes),'spanning_classes_by_states':dict(sorted(collections.Counter(x['states'] for x in classes).items())),'nonspanning_normalized_tables':sum(not c['spanning_roots'] for c in identities.values()),'known_start_occurrences':sum(o['designated_start'] is not None for o in occ),'unknown_start_occurrences':sum(o['designated_start'] is None for o in occ),'excluded_one_state_json_fragments':len(ignored_json),'errors':errors,'elapsed_seconds':round(time.time()-starttime,3)}
 result={'scope':__doc__,'summary':summary,'identities':identities,'classes':classes,'occurrences':occ,'direct_files':direct,'archive_references':archives,'excluded_fragments':ignored_json}
 (out/'census.json').write_text(json.dumps(result,indent=2)+'\n');(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 (out/'frontier194.json').write_text(json.dumps([c for c in classes if c['states']==194],indent=2)+'\n')
 print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=pathlib.Path,required=True);ap.add_argument('--output',type=pathlib.Path,required=True);ap.add_argument('--manifest',type=pathlib.Path)
 a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True);scan(a.root.resolve(),a.output.resolve(),a.manifest)
