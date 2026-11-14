#!/usr/bin/env python3
"""Read-only complete numeric table census; labels/encodings are explicitly scoped."""
import argparse,collections,csv,hashlib,io,json,subprocess,zipfile
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
archive_refs=[];archives=[];seen=set();tables=[];unique={};members=0;errors=[];docs=[]
def table(b,loc):
 try:s=b.decode('utf-8-sig')
 except UnicodeDecodeError:return
 rows={}
 for line in s.splitlines():
  line=line.strip()
  if not line or line.startswith(('#','//',';')):continue
  x=line.split()
  if len(x)!=5 or not x[0].isdigit() or x[1] not in ('0','1') or x[2] not in ('0','1') or x[3] not in ('L','R') or not x[4].isdigit():return
  q,r,w,d,t=x;k=int(q),int(r)
  if k in rows:return
  rows[k]=int(w),d,int(t)
 states={q for q,r in rows}
 if not states or set(rows)!={(q,b) for q in states for b in (0,1)}:return
 halts={t for w,d,t in rows.values()}-states
 if len(halts)!=1:return
 h=sha(b);halt=next(iter(halts))
 tables.append(dict(path=loc,sha256=h,states=len(states),halt=halt))
 if h not in unique:unique[h]=dict(bytes=b,rows=rows,states=states,halt=halt,first_path=loc)
def scan(b,loc,depth):
 global members
 h=sha(b);archive_refs.append(dict(path=loc,sha256=h,depth=depth))
 if h in seen:return
 seen.add(h)
 try:
  with zipfile.ZipFile(io.BytesIO(b)) as z:
   archives.append(dict(path=loc,sha256=h,depth=depth,bytes=len(b),members=len(z.infolist())))
   for i in z.infolist():
    if i.is_dir():continue
    members+=1;n=i.filename;path=loc+'!'+n
    if n.lower().endswith('.zip'):scan(z.read(i),path,depth+1)
    elif n.lower().endswith(('.tm','.txt')):table(z.read(i),path)
 except Exception as e:errors.append(dict(path=loc,error=str(e)))
def canonical(d,root,reflection=False):
 rows=d['rows'];ids={root:0};todo=[root];out=[]
 for q in todo:
  for b in (0,1):
   w,dr,t=rows[q,b]
   if t==d['halt']:v=-1
   else:
    if t not in ids:ids[t]=len(todo);todo.append(t)
    v=ids[t]
   out.append((w, 'L' if dr=='R' else 'R',v) if reflection else (w,dr,v))
 if len(todo)!=len(d['states']):return
 return json.dumps(out,separators=(',',':')).encode()
ps=sorted((a.repo/'docs/incoming').glob('*.zip'))
for j,f in enumerate(ps):
 print('archive',j+1,'/',len(ps),f.name,flush=True);scan(f.read_bytes(),str(f.relative_to(a.repo)),0)
pa=a.repo/'Computability/BusyBeaver/Research/PA'
for f in sorted(pa.rglob('*')):
 if f.is_file() and f.suffix.lower()=='.zip':
  scan(f.read_bytes(),str(f.relative_to(a.repo)),0)
 elif f.is_file() and f.suffix.lower() in ('.tm','.txt'):
  table(f.read_bytes(),str(f.relative_to(a.repo)))
groups=collections.defaultdict(list);raw=[]
for j,(h,d) in enumerate(unique.items()):
 cs=[c for q in sorted(d['states']) if (c:=canonical(d,q)) is not None]
 ch=sha(min(cs)) if cs else None
 d['canonical_graph_sha256']=ch;groups[len(d['states']),ch].append(h)
 raw.append(dict(sha256=h,states=len(d['states']),halt=d['halt'],canonical_graph_sha256=ch,full_reaching_roots=len(cs),first_path=d['first_path']))
 if len(d['states'])<=196:
  (a.output/'tables').mkdir(exist_ok=True);(a.output/'tables'/f'{h}.tm').write_bytes(d['bytes'])
 if j%100==0:print('canonical',j+1,'/',len(unique),flush=True)
summary=dict(commit=subprocess.check_output(['git','-C',str(a.repo),'rev-parse','HEAD'],text=True).strip(),top_level_archives=len(ps),archive_references=len(archive_refs),distinct_archive_bytes=len(archives),max_depth=max(x['depth'] for x in archive_refs),archive_member_occurrences=members,complete_table_occurrences=len(tables),byte_distinct_tables=len(unique),root_free_graph_classes=sum(g is not None for n,g in groups),unrootable_tables=sum(x['canonical_graph_sha256'] is None for x in raw),state_histogram_occurrences=dict(sorted(collections.Counter(t['states'] for t in tables).items())),state_histogram_raw=dict(sorted(collections.Counter(t['states'] for t in raw).items())),state_histogram_graph=dict(sorted(collections.Counter(n for n,g in groups if g is not None).items())),errors=errors,scope='All direct numeric five-column binary .tm/.txt files and ZIPs below PA and all incoming ZIPs recursively by distinct archive byte identity; complete two-row controls and one undefined halt. Code/JSON embedded machines excluded. Graph classes are action-preserving and root-free; two disconnected controls omitted from class count. These are corpus counts, not counts of correct consistency machines.')
classes=[dict(states=n,graph_sha256=g,raw_sha256s=hs,occurrences=[t['path'] for t in tables if t['sha256'] in hs]) for (n,g),hs in groups.items() if n<=196]
(a.output/'census.json').write_text(json.dumps(dict(summary=summary,archives=archives,archive_references=archive_refs,tables=tables,raw_tables=raw,classes_below197=classes),indent=2)+'\n')
with (a.output/'table_occurrences.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=['path','sha256','states','halt']);w.writeheader();w.writerows(tables)
with (a.output/'raw_tables.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(raw[0]));w.writeheader();w.writerows(raw)
print(json.dumps(summary,indent=2))
for c in classes:
 if c['states']<=195:print(c['states'],c['graph_sha256'],c['raw_sha256s'],c['occurrences'][0])
