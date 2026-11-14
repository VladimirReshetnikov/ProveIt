#!/usr/bin/env python3
"""Read-only census of numeric Turing tables and recursively nested research ZIPs.

Adapted from the parser/canonicalizer in the supplied PA194C packet's
comparison/census_current.py. This edition recognizes the relocated PA docs
at the current pinned commit and records optional global reflection hashes.
It does not infer that a table is a correct consistency machine.
"""
from pathlib import Path
import argparse, collections, csv, hashlib, io, json, subprocess, zipfile

ap=argparse.ArgumentParser()
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--incoming',type=Path,help='Incoming ZIP directory; defaults to REPO/docs/incoming.')
ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'census',help='Output directory; defaults to this script’s census subdirectory.')
ap.add_argument('--reuse-cache',action='store_true',help='Explicitly reuse already recorded graph hashes for identical raw bytes. Omit for a fresh independent census.')
args=ap.parse_args()
if not __debug__:ap.error('Assertions are required; do not use Python -O.')
repo=args.repo.resolve(); out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
incoming_dir=(args.incoming or repo/'docs/incoming').resolve()
if not incoming_dir.is_dir():ap.error('Incoming directory does not exist: '+str(incoming_dir))
if not (repo/'Computability/BusyBeaver/Research/PA').is_dir():ap.error('PA research subtree is absent; populate the pinned checkout first.')
def locator(path):
    try:return path.relative_to(repo).as_posix()
    except ValueError:return 'INCOMING/'+path.relative_to(incoming_dir).as_posix()
sha=lambda b:hashlib.sha256(b).hexdigest()
commit=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
assert commit=='17f92105e2bc4317feae6c219cb2143437b482ff'
seen_archives=set();archives=[];refs=[];tables=[];raws={};errors=[];file_count=0

def parse(data):
    try: s=data.decode('utf8')
    except UnicodeDecodeError: return None
    rows={}
    for line in s.splitlines():
        line=line.strip()
        if not line or line.startswith(('#','//',';')):continue
        p=line.split()
        if (len(p)!=5 or p[1] not in ('0','1') or p[2] not in ('0','1')
            or p[3] not in ('L','R') or not p[0].isdigit() or not p[4].isdigit()):return None
        q,r,w,d,t=p;key=(int(q),int(r))
        if key in rows:return None
        rows[key]=(int(w),d,int(t))
    states={q for q,r in rows}
    if not states or set(rows)!={(q,r) for q in states for r in (0,1)}:return None
    halts={t for w,d,t in rows.values()}-states
    if len(halts)!=1:return None
    return rows,states,next(iter(halts))

def add_table(data,path):
    v=parse(data)
    if v is None:return
    rows,states,halt=v;h=sha(data)
    tables.append({'path':path,'sha256':h,'states':len(states),'halt':halt})
    if h not in raws:
        raws[h]={'bytes':data,'rows':rows,'states':states,'halt':halt,'first_path':path}

def scan(data,path,depth):
    global file_count
    h=sha(data);refs.append({'path':path,'sha256':h,'depth':depth})
    if h in seen_archives:return
    seen_archives.add(h)
    try:z=zipfile.ZipFile(io.BytesIO(data))
    except Exception as e:errors.append([path,str(e)]);return
    archives.append({'path':path,'sha256':h,'bytes':len(data),'depth':depth,
                     'file_count':sum(not v.is_dir() for v in z.infolist())})
    for item in z.infolist():
        if item.is_dir():continue
        file_count+=1;name=item.filename;p=path+'!'+name
        if name.lower().endswith('.zip'):scan(z.read(item),p,depth+1)
        elif name.lower().endswith(('.tm','.txt','.tsv','.csv')):add_table(z.read(item),p)

incoming=sorted(incoming_dir.glob('*.zip'))
for j,p in enumerate(incoming):
    print('archive',j+1,len(incoming),p.name,flush=True)
    scan(p.read_bytes(),locator(p),0)
pa=repo/'Computability/BusyBeaver/Research/PA'
for p in sorted(pa.rglob('*')):
    if not p.is_file():continue
    ext=p.suffix.lower()
    if ext in ('.tm','.txt','.tsv','.csv'):add_table(p.read_bytes(),p.relative_to(repo).as_posix())
    elif ext=='.zip':scan(p.read_bytes(),locator(p),0)

def canonical(data,root,mirror=False):
    rows,states,halt=data['rows'],data['states'],data['halt']
    labels={root:0};todo=[root];ans=[]
    for q in todo:
        rr=[]
        for bit in (0,1):
            w,d,t=rows[q,bit]
            if t==halt:k=-1
            else:
                if t not in labels:labels[t]=len(todo);todo.append(t)
                k=labels[t]
            rr.append([w,('R' if d=='L' else 'L') if mirror else d,k])
        ans.append(rr)
    if len(todo)!=len(states):return None
    return json.dumps(ans,separators=(',',':')).encode()

classes=collections.defaultdict(list)
cache_path=out/'census.json'
cache={r['sha256']:r for r in json.loads(cache_path.read_text())['raw_tables']} if args.reuse_cache and cache_path.exists() else {}
for i,(h,d) in enumerate(raws.items()):
    if h in cache:
        old=cache[h]
        d['root_free_sha256']=gh=old['root_free_sha256'];d['reflection_class_sha256']=old['reflection_class_sha256'];d['full_reaching_roots']=old['full_reaching_roots']
        classes[len(d['states']),gh].append(h)
        continue
    cs=[c for q in sorted(d['states']) if (c:=canonical(d,q)) is not None]
    c=min(cs) if cs else None
    gh=sha(c) if c is not None else None
    # Reflect the already serialized canonical root list. Reflection preserves
    # the set of full-reaching roots; JSON substitutions switch only directions.
    mirrorcs=[v.replace(b'"L"',b'"x"').replace(b'"R"',b'"L"').replace(b'"x"',b'"R"') for v in cs]
    gm=sha(min(cs+mirrorcs)) if cs else None
    d['root_free_sha256']=gh;d['reflection_class_sha256']=gm;d['full_reaching_roots']=len(cs)
    classes[len(d['states']),gh].append(h)
    if len(d['states'])<=196:
        dest=out/'tables';dest.mkdir(exist_ok=True);(dest/(h+'.tm')).write_bytes(d['bytes'])
    if i%100==0:print('table',i+1,len(raws),'states',len(d['states']),flush=True)
raw_summary=[{'sha256':h,'states':len(d['states']),'halt':d['halt'],
              'root_free_sha256':d['root_free_sha256'],
              'reflection_class_sha256':d['reflection_class_sha256'],
              'full_reaching_roots':d['full_reaching_roots'],'first_path':d['first_path']}
             for h,d in raws.items()]
summary={'commit':commit,
         'scope':'All incoming ZIPs recursively, plus all numeric .tm/.txt/.tsv/.csv tables and nested ZIPs in PA research, including relocated delivered packets. ZIP byte identities traversed once. Complete numeric two-symbol L/R tables with a single undefined halt target; no source/JSON-only tables. These counts include rejected/experimental tables, partial compilations, and synthetic controls, not only correct consistency machines.',
         'incoming_directory':str(incoming_dir),'graph_hash_cache_used':bool(args.reuse_cache),
         'top_level_incoming_archives':len(incoming),'distinct_archive_bodies':len(archives),
         'archive_references':len(refs),'max_nested_depth':max(x['depth'] for x in refs),
         'archive_member_occurrences':file_count,'complete_table_occurrences':len(tables),
         'distinct_raw_table_bytes':len(raws),
         'root_free_graph_classes':sum(g is not None for n,g in classes),
         'unrootable_raw_tables':sum(d['root_free_sha256'] is None for d in raws.values()),
         'states_histogram_table_occurrences':dict(sorted(collections.Counter(x['states'] for x in tables).items())),
         'states_histogram_raw_tables':dict(sorted(collections.Counter(len(x['states']) for x in raws.values()).items())),
         'states_histogram_root_free_classes':dict(sorted(collections.Counter(n for n,g in classes if g is not None).items())),
         'errors':errors}
occurrences_by_h=collections.defaultdict(list)
for t in tables:occurrences_by_h[t['sha256']].append(t['path'])
output={'summary':summary,'archives':archives,'archive_references':refs,'tables':tables,'raw_tables':raw_summary,
        'classes':[{'states':n,'graph_hash':g,'raw_hashes':hs,
                    'occurrences':[p for h in hs for p in occurrences_by_h[h]]}
                   for (n,g),hs in sorted(classes.items(),key=lambda p:(p[0][0],str(p[0][1])))]}
(out/'census.json').write_text(json.dumps(output,indent=2)+'\n')
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
for name,rows in [('raw_tables',raw_summary),('table_occurrences',tables),('archives',archives)]:
    with (out/(name+'.csv')).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
print(json.dumps(summary,indent=2))
print('194 classes:')
for x in output['classes']:
    if x['states']==194:print(x['graph_hash'],len(x['raw_hashes']),len(x['occurrences']),x['occurrences'][0])
