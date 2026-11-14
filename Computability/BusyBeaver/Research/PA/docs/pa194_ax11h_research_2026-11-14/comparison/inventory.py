#!/usr/bin/env python3
"""Reproducible transition-table census of the pinned PA research corpus.

Read-only with respect to the repository. Nested ZIPs are inspected in memory;
top-level incoming archives are optionally expanded to a private work directory.
The state counts are table properties, never claims of arithmetic calibration.
"""
import argparse
import csv
import hashlib
import io
import json
import re
from collections import Counter, defaultdict
from pathlib import Path, PurePosixPath
import zipfile

PIN = '1c9524d8bf2e0a27b9a16ff622359927f536e663'
PA = 'Computability/BusyBeaver/Research/PA'

def digest(b): return hashlib.sha256(b).hexdigest()

def parse(b):
    rows,declared={},None
    for line in b.decode('ascii').splitlines():
        if not line.strip(): continue
        if line.lstrip().startswith('#'):
            m = re.search(r'\bstart(?:\s+state)?\s*[:=]?\s*(\d+)',line,re.I)
            if m and declared is None: declared=int(m[1])
            continue
        q,r,w,d,n=line.split()
        q,r,w,n=map(int,(q,r,w,n))
        if r not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,r) in rows:
            raise ValueError('bad row '+line)
        rows[q,r]=(w,d,n)
    states={q for q,r in rows}
    if not states or any((q,r) not in rows for q in states for r in (0,1)):
        raise ValueError('incomplete table')
    if declared is not None:
        start=declared; basis='comment'
    elif sorted(states)==list(range(len(states))):
        start=0; basis='dense convention; not independently confirmed'
    else:
        start=None; basis='unspecified'
    if start is not None and start not in states: raise ValueError('bad start')
    return rows,states,start,basis

def rooted(rows,states,start,mirror=False,loose=False):
    index={start:0}; order=[start]; out=[]
    for q in order:
        for r in (0,1):
            w,d,n=rows[q,r]
            if mirror: d='L' if d=='R' else 'R'
            if n in states:
                if n not in index: index[n]=len(index); order.append(n)
                out.append((w,d,index[n]))
            else: out.append((0,'R',-1) if loose else (w,d,-1))
    return digest(json.dumps(out,separators=(',',':')).encode()),len(order)

def classify(b):
    rows,states,start,basis=parse(b)
    roots=[rooted(rows,states,q) for q in states]
    maximum=max(n for h,n in roots)
    # This is a complete graph invariant when some root sees every state;
    # otherwise it identifies only maximal reachable components.
    table=min(h for h,n in roots if n==maximum)
    mirrors=[rooted(rows,states,q,mirror=True) for q in states]
    table_mirror=min([table]+[h for h,n in mirrors if n==maximum])
    a={'states':len(states),'rows':len(rows),'start':start,'start_basis':basis,
       'maximum_reachable':maximum,'table_class':table,
       'table_class_complete':maximum==len(states),
       'table_reflection_class':table_mirror,
       'halt_labels':sorted({n for w,d,n in rows.values()}-states),
       'normalized_sha256':digest(json.dumps(sorted((q,r,w,d,n) for (q,r),(w,d,n) in rows.items()),separators=(',',':')).encode())}
    if start is not None:
        a['rooted_class'],a['reachable']=rooted(rows,states,start)
        a['rooted_reflection_class']=min(a['rooted_class'],rooted(rows,states,start,True)[0])
        a['rooted_loose_reflection_class']=min(rooted(rows,states,start,loose=True)[0],rooted(rows,states,start,mirror=True,loose=True)[0])
    else: a.update(rooted_class=None,reachable=None,rooted_reflection_class=None,rooted_loose_reflection_class=None)
    return a

def decode_json_table(node):
    """Recognize explicit transition data, never execute a source generator."""
    def nat(x): return type(x)==int and x>=0
    def direction(x): return not isinstance(x,bool) and x in ('L','R',-1,1)
    def act(x): return isinstance(x,list) and len(x)==3 and type(x[0])==int and x[0] in (0,1) and direction(x[1]) and nat(x[2])
    def norm(x):
        w,d,t=x
        return w,('L' if d==-1 else 'R' if d==1 else d),t
    def record(x):
        if not isinstance(x,dict): return None
        def get(names):
            for k in names:
                if k in x:return x[k]
        q=get(('state','source','q','current_state','from')); b=get(('read','symbol','read_bit','read_symbol','b'))
        w=get(('write','write_bit','write_symbol','w')); d=get(('direction','move','dir','d')); t=get(('next','target','next_state','to','t'))
        if nat(q) and type(b)==int and b in (0,1) and type(w)==int and w in (0,1) and direction(d) and nat(t):return q,b,w,d,t
    if isinstance(node,str) and '\n' in node:
        try:
            b=node.encode('ascii'); rows,states,start,basis=parse(b)
            if len(states)>=2:return b
        except Exception: pass
        return None
    rows=[]
    if isinstance(node,list) and len(node)>=2:
        if all(isinstance(x,list) and len(x)==5 and nat(x[0]) and type(x[1])==int and x[1] in (0,1) and type(x[2])==int and x[2] in (0,1) and direction(x[3]) and nat(x[4]) for x in node):
            rows=[(q,b,*norm((w,d,t))) for q,b,w,d,t in node]
        elif all(isinstance(x,list) and len(x)==2 and all(act(a) for a in x) for x in node):
            rows=[(q,b,*norm(a)) for q,pair in enumerate(node) for b,a in enumerate(pair)]
        elif len(node)%2==0 and all(act(x) for x in node):
            rows=[(i//2,i%2,*norm(x)) for i,x in enumerate(node)]
        elif all(record(x) is not None for x in node):
            rows=[(q,b,*norm((w,d,t))) for q,b,w,d,t in map(record,node)]
    elif isinstance(node,dict) and node:
        if all(k.isdigit() and isinstance(v,list) and len(v)==2 and all(act(a) for a in v) for k,v in node.items()):
            rows=[(int(q),b,*norm(a)) for q,pair in node.items() for b,a in enumerate(pair)]
        elif all(re.fullmatch(r'\(?\s*\d+\s*[,;:]\s*[01]\s*\)?',k) and act(v) for k,v in node.items()):
            rows=[(*map(int,re.findall(r'\d+',k)),*norm(v)) for k,v in node.items()]
    if not rows:return None
    b=('\n'.join(' '.join(map(str,r)) for r in sorted(rows))+'\n').encode()
    try:
        _,states,_,_=parse(b)
        if len(states)>=2:return b
    except Exception: pass
    return None

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('repository'); ap.add_argument('out'); ap.add_argument('--extract',action='store_true'); args=ap.parse_args()
    repo=Path(args.repository).resolve(); out=Path(args.out).resolve(); out.mkdir(exist_ok=True,parents=True)
    cache={}; tables=[]; archives=[]; errors=[]; zip_seen={}
    prior=out/'tables.json'
    if prior.exists():
        for x in json.loads(prior.read_text()):
            cache[x['sha256']]={k:v for k,v in x.items() if k not in ('path','bytes','sha256')}
    def process(data,path):
        sha=digest(data)
        if sha not in cache:
            try: cache[sha]=classify(data)
            except Exception as e: cache[sha]={'error':repr(e)}
        obj={'path':path,'bytes':len(data),'sha256':sha,**cache[sha]}
        if 'error' in obj: errors.append(obj)
        else:
            tables.append(obj)
            rep=out/'representatives'/(obj['table_class']+'.tm')
            if not rep.exists():
                rep.parent.mkdir(exist_ok=True); rep.write_bytes(data)
    def json_candidates(value,pointer='$'):
        data=decode_json_table(value)
        if data is not None:
            yield pointer,data; return
        if isinstance(value,list):
            for i,x in enumerate(value): yield from json_candidates(x,pointer+'/'+str(i))
        elif isinstance(value,dict):
            for k,x in value.items(): yield from json_candidates(x,pointer+'/'+str(k))
    def inspect(data,path,depth=0):
        suffix=Path(path).suffix.lower()
        if suffix=='.tm': process(data,path)
        elif suffix in ('.txt','.tsv','.csv'):
            try: parse(data)
            except Exception: return
            process(data,path)
        elif suffix=='.json':
            try: value=json.loads(data)
            except Exception: return
            for pointer,d in json_candidates(value): process(d,path+'::JSON'+pointer)
        elif suffix=='.zip': zscan(data,path,depth=depth+1)
    def zscan(data,path,extract_dir=None,depth=0):
        sha=digest(data)
        if depth>12: raise ValueError('excessive archive nesting')
        archive={'path':path,'sha256':sha,'compressed_bytes':len(data)}
        if sha in zip_seen:
            archive['duplicate_of']=zip_seen[sha]; archives.append(archive); return
        zip_seen[sha]=path
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            infos=z.infolist(); archive['members']=len(infos); archive['uncompressed_bytes']=sum(x.file_size for x in infos); archives.append(archive)
            if archive['uncompressed_bytes']>2_000_000_000: raise ValueError('archive expansion limit')
            for inf in infos:
                pp=PurePosixPath(inf.filename)
                if pp.is_absolute() or '..' in pp.parts or (inf.external_attr>>16)&0o170000==0o120000:
                    raise ValueError('unsafe archive entry '+inf.filename)
                if inf.is_dir(): continue
                content=z.read(inf)
                if extract_dir is not None:
                    dest=extract_dir.joinpath(*pp.parts); dest.parent.mkdir(exist_ok=True,parents=True); dest.write_bytes(content)
                key=path+'!'+inf.filename
                inspect(content,key,depth)
    for p in sorted((repo/PA).rglob('*')):
        if not p.is_file(): continue
        if p.suffix.lower() in ('.tm','.txt','.tsv','.csv','.json','.zip'):
            inspect(p.read_bytes(),p.relative_to(repo).as_posix())
    for p in sorted((repo/'docs/incoming').glob('*.zip')):
        zscan(p.read_bytes(),p.relative_to(repo).as_posix(),out/'incoming'/p.stem if args.extract else None)
    (out/'tables.json').write_text(json.dumps(tables,indent=2)+'\n')
    (out/'archives.json').write_text(json.dumps(archives,indent=2)+'\n')
    (out/'parse_errors.json').write_text(json.dumps(errors,indent=2)+'\n')
    groups=defaultdict(list)
    for x in tables: groups[x['table_class']].append(x)
    classes=[]
    for cl,items in sorted(groups.items()):
        representative=min(items,key=lambda x:(not ('docs/incoming' in x['path']),len(x['path']),x['path']))
        classes.append({'table_class':cl,'table_reflection_class':representative['table_reflection_class'],'states':representative['states'],
             'maximum_reachable':representative['maximum_reachable'],'complete_invariant':representative['table_class_complete'],
             'representative':representative['path'],'occurrences':len(items),'paths':[x['path'] for x in items],
             'distinct_bytes':len({x['sha256'] for x in items}),'rooted_classes':sorted({x['rooted_class'] for x in items if x['rooted_class']})})
    (out/'classes.json').write_text(json.dumps(classes,indent=2)+'\n')
    cols=['states','maximum_reachable','table_class','table_reflection_class','complete_invariant','occurrences','distinct_bytes','representative']
    with (out/'classes.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=cols);w.writeheader();w.writerows({k:x[k] for k in cols} for x in classes)
    cols=['path','bytes','sha256','states','rows','start','start_basis','reachable','table_class','rooted_class']
    with (out/'tables.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=cols);w.writeheader();w.writerows({k:x[k] for k in cols} for x in tables)
    summary={'commit':PIN,'scope':[PA,'docs/incoming'],'valid_table_occurrences':len(tables),'distinct_table_bytes':len({x['sha256'] for x in tables}),
       'table_classes':len(classes),'reflection_classes':len({x['table_reflection_class'] for x in classes}),
       'classes_by_states':dict(sorted(Counter(x['states'] for x in classes).items())),
       'classes_without_a_root_reaching_every_state':[x['table_class'] for x in classes if not x['complete_invariant']],
       'parse_errors':len(errors),'archives':len(archives),'unique_archive_bytes':len(zip_seen),
       'notes':['Counts concern stored transition graphs, not certified consistency machines.',
                'Dense table state 0 is a convention unless a start is declared; native tables may omit starts.',
                'Top-level source trees are read recursively; ZIP members (including nested ZIPs) are inspected.',
                'Recognized encodings: complete five-column literal .tm/.txt/.tsv/.csv and explicit JSON text, row arrays, paired or flat action arrays, numeric-state dictionaries, transition-key dictionaries and row records; signed moves are normalized. One-state JSON fragments are excluded. Programmatically specified machines are not executed.',
                'Duplicate nested ZIP bytes are represented by an archive duplicate_of link, not re-expanded.',
                'Machine tables omitted by repository deduplication are recorded in upstream MACHINE_FILES.tsv, not counted as new stored occurrences.']}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n'); print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
