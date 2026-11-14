#!/usr/bin/env python3
"""Independent, read-only census of retained PA files and recursively nested ZIPs.

Recognizes complete five-column numeric binary tables and explicit JSON arrays,
row records, paired/flat action lists and numeric or (state,read) dictionaries.
It does not execute generators or infer machines from mathematical prose.
"""
from pathlib import Path
import argparse,collections,csv,hashlib,io,json,os,re,subprocess,sys,zipfile

ROOT=Path(__file__).resolve().parent.parent
REPO=ROOT/'ProveIt'
OUT=Path(os.environ.get('PA194_CENSUS_OUTPUT',str(ROOT/'analysis/census')))
REV='1c9524d8bf2e0a27b9a16ff622359927f536e663'
SCOPES=['Computability/BusyBeaver/Research/PA','docs/incoming']
TEXT={'.tm','.txt','.csv','.tsv'}
sha=lambda b:hashlib.sha256(b).hexdigest()

def validate(rows):
    states={q for q,b in rows}
    if not states or len(rows)!=2*len(states):return None
    if any((q,b) not in rows for q in states for b in (0,1)):return None
    halts={v[2] for v in rows.values()}-states
    if len(halts)!=1:return None
    return rows,states,next(iter(halts))

def parse(data):
    try:s=data.decode('ascii')
    except UnicodeDecodeError:return None
    rows={};declared=None
    for line in s.splitlines():
        line=line.strip()
        if not line:continue
        if line.startswith('#'):
            m=re.search(r'\bstart\s*[:=]?\s*(\d+)\b',line,re.I)
            if m and declared is None:declared=int(m[1])
            continue
        a=re.split(r'[,\s]+',line)
        if len(a)!=5 or a[3] not in ('L','R'):return None
        try:q,b,w,n=map(int,(a[0],a[1],a[2],a[4]))
        except ValueError:return None
        if q<0 or n<0 or b not in (0,1) or w not in (0,1) or (q,b) in rows:return None
        rows[q,b]=(w,a[3],n)
    v=validate(rows)
    if v is None or declared is not None and declared not in v[1]:return None
    return (*v,declared)

def integer(x):return type(x) is int and x>=0
def direction(x):return type(x) is not bool and x in ('L','R',-1,1)
def action(x):return isinstance(x,list) and len(x)==3 and type(x[0]) is int and x[0] in (0,1) and direction(x[1]) and integer(x[2])
def norm(a):return (a[0],'L' if a[1]==-1 else 'R' if a[1]==1 else a[1],a[2])
def rowrecord(x):
    if not isinstance(x,dict):return None
    def get(names):return next((x[n] for n in names if n in x),None)
    q=get(['state','source','q','current_state','from']);b=get(['read','symbol','read_bit','read_symbol','b'])
    w=get(['write','write_bit','write_symbol','w']);d=get(['direction','move','dir','d']);t=get(['next','target','next_state','to','t'])
    if integer(q) and type(b) is int and b in (0,1) and type(w) is int and w in (0,1) and direction(d) and integer(t):return q,b,w,d,t

def decode(node):
    if isinstance(node,str) and '\n' in node:
        try:return parse(node.encode('ascii'))
        except UnicodeEncodeError:return None
    rows={}
    if isinstance(node,list) and len(node)>=2:
        if all(isinstance(x,list) and len(x)==5 and integer(x[0]) and type(x[1]) is int and x[1] in (0,1) and type(x[2]) is int and x[2] in (0,1) and direction(x[3]) and integer(x[4]) for x in node):
            for q,b,w,d,t in node:
                if (q,b) in rows:return None
                rows[q,b]=norm([w,d,t])
        elif all(isinstance(x,list) and len(x)==2 and all(action(a) for a in x) for x in node):
            rows={(q,b):norm(a) for q,pair in enumerate(node) for b,a in enumerate(pair)}
        elif len(node)%2==0 and all(action(a) for a in node):rows={(i//2,i%2):norm(a) for i,a in enumerate(node)}
        elif all(rowrecord(x) is not None for x in node):
            for q,b,w,d,t in map(rowrecord,node):
                if (q,b) in rows:return None
                rows[q,b]=norm([w,d,t])
    elif isinstance(node,dict) and node:
        if all(k.isdigit() and isinstance(v,list) and len(v)==2 and all(action(a) for a in v) for k,v in node.items()):rows={(int(q),b):norm(a) for q,pair in node.items() for b,a in enumerate(pair)}
        elif all(re.fullmatch(r'\(?\s*\d+\s*[,;:]\s*[01]\s*\)?',k) and action(v) for k,v in node.items()):
            for k,v in node.items():
                q,b=map(int,re.findall(r'\d+',k));rows[q,b]=norm(v)
    v=validate(rows)
    return (*v,None) if v else None

def canonical(rows,states,start,mirror=False,complement=False,loose=False):
    index={start:0};order=[start];out=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b^complement];w^=complement
            if mirror:d='L' if d=='R' else 'R'
            if n in states:
                if n not in index:index[n]=len(order);order.append(n)
                out.append((w,d,index[n]))
            else:out.append((0,'R',-1) if loose else (w,d,-1))
    return tuple(out),len(order)

def eligible_roots(rows,states):
    order=sorted(states);index={q:i for i,q in enumerate(order)}
    reach=[1<<i for i in range(len(order))]
    edges=[[index[n] for b in (0,1) if (n:=rows[q,b][2]) in states] for q in order]
    changed=True
    while changed:
        changed=False
        for i,targets in enumerate(edges):
            v=reach[i]
            for j in targets:v|=reach[j]
            if v!=reach[i]:reach[i]=v;changed=True
    maximum=max(v.bit_count() for v in reach)
    return [q for q,v in zip(order,reach) if v.bit_count()==maximum],maximum

occ=[];classes={};raw_cache={};json_cache={};zip_seen={};archives=[];warnings=[];scanned=collections.Counter();source_files=[];known_by_bytes={}
def normalized(rows):return ''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(rows.items())).encode()

def record(data,parsed,path,kind):
    rows,states,halt,declared=parsed
    txt=normalized(rows);key=sha(txt)
    start=declared if declared is not None else 0 if sorted(states)==list(range(len(states))) else None
    if key not in classes:
        eligible,maximum=eligible_roots(rows,states)
        reused=known_by_bytes.get(sha(data)) or known_by_bytes.get(key)
        if reused is not None and int(reused['states'])==len(states):
            best=reused['table_class'];roots={};scanned['catalogue_byte_identities_reused']+=1
        else:
            roots={q:canonical(rows,states,q) for q in eligible}
            best=min(sha(json.dumps(t,separators=(',',':')).encode()) for t,n in roots.values() if n==maximum)
            scanned['fresh_labeled_classifications']+=1
        classes[key]={'states':len(states),'table_class':best,'max_reachable':maximum,'halt':halt,'normalized_sha256':key,'representative':path,'_rows':rows,'_states':states,'_roots':roots,'_eligible':eligible}
    c=classes[key]
    if start is not None and start not in c['_roots']:c['_roots'][start]=canonical(rows,states,start)
    occ.append({'path':path,'kind':kind,'bytes':len(data),'raw_sha256':sha(data),'normalized_sha256':key,'states':len(states),'halt':halt,'table_class':c['table_class'],'max_reachable':c['max_reachable'],'start':start,'start_basis':'declared' if declared is not None else 'dense_zero_convention' if start==0 else 'unspecified','rooted_sha256':sha(json.dumps(c['_roots'][start][0],separators=(',',':')).encode()) if start is not None else None,'reachable_from_start':c['_roots'][start][1] if start is not None else None})

def inspect_json(data,path):
    scanned['json']+=1;digest=sha(data)
    if digest in json_cache:
        for ptr,pdata,parsed in json_cache[digest]:record(pdata,parsed,path+'::json:'+ptr,'json')
        return
    found=[];json_cache[digest]=found
    if not any(tok in data for tok in (b'"L"',b'"R"',b' L ',b' R ',b'"table"',b'"transitions"')) and not re.search(rb'\[\s*\d+\s*,\s*[01]\s*,\s*[01]\s*,\s*-?1\s*,|\[\s*[01]\s*,\s*-?1\s*,\s*\d+\s*\]|"(?:direction|move|dir|d)"\s*:\s*-?1',data):return
    try:obj=json.loads(data)
    except (ValueError,UnicodeDecodeError) as e:warnings.append({'path':path,'reason':'json_parse','message':str(e)});return
    todo=[('$',obj)]
    while todo:
        ptr,node=todo.pop();p=decode(node)
        if p and len(p[1])>=2:
            txt=normalized(p[0]);found.append((ptr,txt,p));record(txt,p,path+'::json:'+ptr,'json');continue
        if isinstance(node,dict):todo.extend((ptr+'/'+str(k).replace('~','~0').replace('/','~1'),v) for k,v in node.items() if isinstance(v,(list,dict,str)))
        elif isinstance(node,list):todo.extend((ptr+'/'+str(i),v) for i,v in enumerate(node) if isinstance(v,(list,dict,str)))

def inspect(data,path,depth=0):
    ext=Path(path.split('!')[-1]).suffix.lower()
    if ext=='.zip':
        digest=sha(data);archives.append({'path':path,'sha256':digest,'bytes':len(data),'deduplicated':digest in zip_seen})
        if digest in zip_seen:return
        zip_seen[digest]=path
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for info in z.infolist():
                if not info.is_dir() and Path(info.filename).suffix.lower() in TEXT|{'.json','.zip'}:inspect(z.read(info),path+'!'+info.filename,depth+1)
        return
    if ext=='.json':inspect_json(data,path);return
    if ext not in TEXT:return
    scanned['literal']+=1;digest=sha(data)
    if digest not in raw_cache:raw_cache[digest]=parse(data)
    if raw_cache[digest]:record(data,raw_cache[digest],path,'literal')

def main():
    global REPO, OUT, REV
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--revision',default=REV)
    args=parser.parse_args()
    REPO=args.repo.resolve();OUT=args.output.resolve();REV=args.revision
    OUT.mkdir(parents=True,exist_ok=True)
    master=list(csv.DictReader(open(REPO/'Computability/BusyBeaver/Research/PA/docs/MACHINES.tsv'),delimiter='\t'))
    by_id={r['class']:r for r in master}
    for row in csv.DictReader(open(REPO/'Computability/BusyBeaver/Research/PA/docs/MACHINE_FILES.tsv'),delimiter='\t'):
        known_by_bytes[row['sha256']]=by_id[row['class']]
    tree=subprocess.check_output(['git','-C',str(REPO),'ls-tree','-rz',REV,'--',*SCOPES])
    needed=[]
    for rec in tree.split(b'\0'):
        if not rec:continue
        meta,p=rec.split(b'\t',1);mode,kind,oid=meta.decode().split();path=p.decode()
        if kind!='blob' or Path(path).suffix.lower() not in TEXT|{'.json','.zip'}:continue
        needed.append((path,oid))
    missing=[(p,o) for p,o in needed if not (REPO/p).exists()]
    print('tracked inputs',len(needed),'missing worktree blobs',len(missing),flush=True)
    for i,(path,oid) in enumerate(needed):
        fp=REPO/path
        data=fp.read_bytes() if fp.exists() else subprocess.check_output(['git','-C',str(REPO),'cat-file','blob',oid])
        size=len(data)
        if hashlib.sha1(b'blob '+str(size).encode()+b'\0'+data).hexdigest()!=oid:raise RuntimeError('Git identity mismatch '+path)
        source_files.append({'path':path,'git_blob':oid,'bytes':size});inspect(data,path)
        if i%500==0:print('scanned',i,'/',len(needed),'tables',len(occ),'labeled',len(classes),flush=True)
    grouped=collections.defaultdict(list)
    for r in occ:grouped[r['table_class']].append(r)
    known={r['table_class']:r for r in csv.DictReader(open(REPO/'Computability/BusyBeaver/Research/PA/docs/MACHINES.tsv'),delimiter='\t')}
    cls=[]
    for key,group in sorted(grouped.items(),key=lambda kv:(kv[1][0]['states'],kv[0])):
        g=group[0];k=known.get(key);entry={'table_class':key,'states':g['states'],'max_reachable':g['max_reachable'],'occurrences':len(group),'distinct_raw_sha256':len({r['raw_sha256'] for r in group}),'distinct_normalized_tables':len({r['normalized_sha256'] for r in group}),'existing_class':k['class'] if k else None,'first_packet':k['first_packet'] if k else None,'representative':k['kept_file'] if k else g['path'],'paths':sorted(r['path'] for r in group)}
        if g['states']==194 and g['max_reachable']==194:
            c=classes[g['normalized_sha256']];forms=[]
            for mirror in (False,True):
                for comp in (False,True):
                    for q in c['_eligible']:
                        t,n=canonical(c['_rows'],c['_states'],q,mirror,comp,True)
                        if n==194:forms.append(t)
            smallest=min(forms);entry['extended_class_sha256']=sha(json.dumps(smallest,separators=(',',':')).encode());entry['extended_canonical']=smallest
        cls.append(entry)
    spanning={(r['states'],r['table_class']) for r in occ if r['states']==r['max_reachable']}
    summary={'revision':REV,'tracked_candidate_files':len(needed),'literal_files_examined':scanned['literal'],'json_files_examined':scanned['json'],'literal_and_json_table_occurrences':len(occ),'distinct_raw_table_bytes':len({r['raw_sha256'] for r in occ}),'distinct_labeled_transition_tables':len(classes),'table_classes':len(cls),'classes_by_states':dict(sorted(collections.Counter(c['states'] for c in cls).items())),'full_spanning_graph_classes':len(spanning),'full_spanning_classes_by_states':dict(sorted(collections.Counter(n for n,h in spanning).items())),'existing_catalogue_classes':len(known),'catalogue_classes_recovered':len(set(known)&set(grouped)),'new_classes_vs_catalogue':len(set(grouped)-set(known)),'archive_occurrences':len(archives),'distinct_archives':len(zip_seen),'catalogue_byte_identities_reused':scanned['catalogue_byte_identities_reused'],'fresh_labeled_classifications':scanned['fresh_labeled_classifications'],'warnings':warnings,'scope':__doc__,'notes':['Every candidate file is read and checked against its pinned Git blob SHA.','Existing all-size catalogue identities may be reused only after exact table byte-hash agreement; new labeled identities are computed directly.','The separate portable novelty check reparses and recomputes every 194-state frontier graph independently.','Recognition requires exactly one external terminal target; no-terminal diagnostic graphs and one-state embedded JSON fragments are excluded.','Identical nested ZIP payloads are traversed once; archive aliases are recorded.','Nonspanning table_class values identify maximum reachable components, as in the repository index; use full_spanning_graph_classes for whole-graph counts.']}
    for name,data in [('summary.json',summary),('occurrences.json',occ),('classes.json',cls),('archives.json',archives),('tracked_inputs.json',source_files)]: (OUT/name).write_text(json.dumps(data,indent=2)+'\n')
    for name,data in [('occurrences.csv',occ),('classes.csv',[{k:v for k,v in x.items() if k!='extended_canonical'} for x in cls])]:
        with (OUT/name).open('w',newline='') as f:
            fields=list(dict.fromkeys(k for x in data for k in x))
            w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows({k:json.dumps(v) if isinstance(v,(list,dict)) else v for k,v in x.items()} for x in data)
    print(json.dumps(summary,indent=2),flush=True)

if __name__=='__main__':main()
