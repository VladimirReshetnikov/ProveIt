# Adapted from the prior PA194 comparison/census.py; see report for attribution.
from pathlib import Path
import subprocess,zipfile,io,hashlib,json,re,collections
import argparse
ap=argparse.ArgumentParser(description='Read-only recursive census of the pinned PA research corpus.')
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args()
REPO=args.repo.resolve();OUT=args.output.resolve();OUT.mkdir(parents=True,exist_ok=True)
assert subprocess.check_output(['git','-C',str(REPO),'rev-parse','HEAD']).decode().strip()=='768c2be1a8e4d2fcf8aa3443c7b0f084d145734c', 'Use the pinned repository snapshot.'
sha=lambda b:hashlib.sha256(b).hexdigest()
seen_archives=set();archives=[];refs=[];tables=[];raws={};count_files=0;errors=[]
def parse(b):
 try:s=b.decode('utf8')
 except:return
 rows={}
 for l in s.splitlines():
  l=l.strip()
  if not l or l.startswith(('#','//',';')):continue
  p=l.split()
  if len(p)!=5 or p[1] not in ['0','1'] or p[2] not in ['0','1'] or p[3] not in ['L','R'] or not p[0].isdigit() or not p[4].isdigit():return
  q,r,w,d,t=p;key=int(q),int(r)
  if key in rows:return
  rows[key]=int(w),d,int(t)
 states={q for q,r in rows}
 if not states or set(rows)!={(q,r) for q in states for r in (0,1)}:return
 halts={t for w,d,t in rows.values()}-states
 if len(halts)!=1:return
 return rows,states,next(iter(halts))
def add_table(b,path):
 z=parse(b)
 if z is None:return
 rows,states,halt=z;h=sha(b)
 tables.append({'path':path,'sha256':h,'states':len(states),'halt':halt})
 if h not in raws:
  raws[h]={'bytes':b,'rows':rows,'states':states,'halt':halt,'first_path':path}
def scan(b,path,depth):
 global count_files
 h=sha(b);refs.append({'path':path,'sha256':h,'depth':depth})
 if h in seen_archives:return
 seen_archives.add(h)
 try:z=zipfile.ZipFile(io.BytesIO(b))
 except Exception as e:errors.append([path,str(e)]);return
 archives.append({'path':path,'sha256':h,'bytes':len(b),'depth':depth,'file_count':sum(not i.is_dir() for i in z.infolist())})
 for i in z.infolist():
  if i.is_dir():continue
  count_files+=1;n=i.filename;p=path+'!'+n
  if n.lower().endswith('.zip'):
   scan(z.read(i),p,depth+1)
  elif n.lower().endswith(('.tm','.txt')):
   add_table(z.read(i),p)
paths=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-r','--name-only','HEAD','docs/incoming']).decode().splitlines()
paths=[p for p in paths if p.endswith('.zip')]
for j,p in enumerate(paths):
 print('archive',j+1,len(paths),p,flush=True)
 scan(subprocess.check_output(['git','-c','core.packedGitWindowSize=4m','-c','core.packedGitLimit=32m','-c','core.deltaBaseCacheLimit=16m','-C',str(REPO),'show','HEAD:'+p]),p,0)
for p in sorted((REPO/'Computability/BusyBeaver/Research/PA').rglob('*.tm')):
 add_table(p.read_bytes(),str(p.relative_to(REPO)))

def canonical(data,root):
 rows,states,halt=data['rows'],data['states'],data['halt'];labels={root:0};todo=[root];ans=[]
 for q in todo:
  rr=[]
  for bit in (0,1):
   w,d,t=rows[q,bit]
   if t==halt:k=-1
   else:
    if t not in labels:labels[t]=len(todo);todo.append(t)
    k=labels[t]
   rr.append([w,d,k])
  ans.append(rr)
 if len(todo)!=len(states):return None
 return json.dumps(ans,separators=(',',':')).encode()
classes=collections.defaultdict(list)
for i,(h,d) in enumerate(raws.items()):
 # Exact root-free canonicalization among starts reaching the full working graph.
 cs=[c for q in sorted(d['states']) if (c:=canonical(d,q)) is not None]
 c=min(cs) if cs else None
 gh=sha(c) if c is not None else None
 d['root_free_sha256']=gh
 d['full_reaching_roots']=len(cs)
 classes[len(d['states']),gh].append(h)
 if len(d['states'])<=195:
  (OUT/(h+'.tm')).write_bytes(d['bytes'])
 print('table',i+1,len(raws),'states',len(d['states']),flush=True) if i%100==0 else None
summary={
 'commit':subprocess.check_output(['git','-C',str(REPO),'rev-parse','HEAD']).decode().strip(),
 'scope':'All top-level incoming ZIPs at the pinned revision, recursively traversing each archive byte identity once; complete numeric binary .tm and .txt tables with one undefined halt target; direct PA .tm files. Code/JSON-embedded tables and a no-halt synthetic 4-state control are excluded. Graph classification excludes two disconnected synthetic controls.',
 'top_level_archives':len(paths),'distinct_archive_bodies':len(archives),'archive_references':len(refs),
 'max_nested_depth':max(x['depth'] for x in refs),'distinct_archive_body_member_occurrences':count_files,
 'complete_table_occurrences':len(tables),'distinct_raw_table_bytes':len(raws),
 'root_free_graph_classes':sum(h is not None for n,h in classes),'root_free_graph_class_count_excludes_disconnected_controls':True,'unrootable_raw_tables':sum(d['root_free_sha256'] is None for d in raws.values()),
 'states_histogram_table_occurrences':dict(sorted(collections.Counter(x['states'] for x in tables).items())),
 'states_histogram_raw_tables':dict(sorted(collections.Counter(len(x['states']) for x in raws.values()).items())),
 'states_histogram_root_free_classes':dict(sorted(collections.Counter(n for n,h in classes if h is not None).items())),
 'errors':errors}
output={'summary':summary,'archives':archives,'archive_references':refs,'tables':tables,
'raw_tables':[{'sha256':h,'states':len(d['states']),'halt':d['halt'],'root_free_sha256':d['root_free_sha256'],'full_reaching_roots':d['full_reaching_roots'],'first_path':d['first_path']} for h,d in raws.items()],
'classes':[{'states':n,'graph_hash':g,'raw_hashes':hs,'occurrences':[x['path'] for x in tables if x['sha256'] in hs]} for (n,g),hs in classes.items()]}
(OUT/'census.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(summary,indent=2));print('all classes:',len(output['classes']))
for x in output['classes']:
 if x['states']>195:continue
 print(x['graph_hash'],len(x['raw_hashes']),len(x['occurrences']),x['occurrences'][0])
