#!/usr/bin/env python3
"""Read-only census of complete numeric binary TM tables in the pinned PA tree.

Recognizes .tm/.txt/.tsv/.csv files plus complete textual/five-column array
tables embedded in JSON, recursively including ZIP files. It does not infer
machines from program source or arbitrary JSON transition dictionaries.
Only structural counts are recomputed; logical claims need separate review.
"""
from pathlib import Path
from collections import Counter
import csv, hashlib, io, json, re, sys, zipfile, argparse

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('repo',type=Path)
ap.add_argument('output',type=Path)
ap.add_argument('--incoming',type=Path,required=True)
args=ap.parse_args()
ROOT=args.repo.resolve()
OUT=args.output.resolve()
OUT.mkdir(parents=True, exist_ok=True)
cache, occurrences, rejected, json_errors, archives = {}, [], [], [], {}

def parse(data):
    try: text=data.decode('ascii')
    except UnicodeDecodeError: return None
    rows={}; declared=None
    for line in text.splitlines():
        line=line.strip()
        if not line: continue
        if line.startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',line)
            if m and declared is None: declared=int(m[1])
            continue
        s=line.split()
        if len(s)!=5 or s[1] not in ('0','1') or s[2] not in ('0','1') or s[3] not in ('L','R'): return None
        try: q,b,w,n=int(s[0]),int(s[1]),int(s[2]),int(s[4])
        except ValueError:return None
        if min(q,n)<0 or (q,b) in rows:return None
        rows[q,b]=(w,s[3],n)
    states={q for q,b in rows}
    if not states or len(rows)!=2*len(states):return None
    halts=sorted({n for w,d,n in rows.values()}-states)
    start=declared if declared is not None else (0 if states==set(range(len(states))) else None)
    if start is not None and start not in states:return None
    return rows,states,start,declared,halts

def rooted(rows,states,start):
    index={start:0}; order=[start]; actions=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b]
            if n in states:
                if n not in index:index[n]=len(order);order.append(n)
                actions.append((w,d,index[n]))
            else:actions.append((w,d,-1))
    return hashlib.sha256(json.dumps(actions,separators=(',',':')).encode()).hexdigest(),len(order)

def classify(data, table):
    digest=hashlib.sha256(data).hexdigest()
    if digest in cache:return cache[digest]
    rows,states,start,declared,halts=table
    roots={q:rooted(rows,states,q) for q in states}
    most=max(x[1] for x in roots.values())
    rootfree=min(h for h,n in roots.values() if n==most)
    ans=dict(sha256=digest,states=len(states),rows=len(rows),start=start,
             declared_start=declared,halt_labels=halts,max_reachable=most,
             has_spanning_root=(most==len(states)),table_class=rootfree,
             machine_class=None if start is None else roots[start][0],
             start_reachable=None if start is None else roots[start][1])
    rep=OUT/'representatives'/(rootfree+'.tm')
    rep.parent.mkdir(exist_ok=True)
    if not rep.exists():rep.write_bytes(data)
    cache[digest]=ans
    return ans

def json_candidates(value,pointer='$'):
    if isinstance(value,str):
        if '\n' in value and len(value)>30:
            try:data=value.encode('ascii')
            except UnicodeEncodeError:return
            p=parse(data)
            if p:yield pointer,data,p
    elif isinstance(value,list):
        if len(value)>=2 and all(isinstance(x,list) and len(x)==5 and type(x[0])==int and x[1] in (0,1) and x[2] in (0,1) and x[3] in ('L','R') and type(x[4])==int for x in value):
            data=('\n'.join(' '.join(map(str,x)) for x in value)+'\n').encode()
            p=parse(data)
            if p:yield pointer,data,p
        else:
            for i,x in enumerate(value):yield from json_candidates(x,pointer+'/'+str(i))
    elif isinstance(value,dict):
        for k,x in value.items():yield from json_candidates(x,pointer+'/'+str(k))

def inspect(name,data):
    suffix=Path(name).suffix.lower()
    if suffix in ('.tm','.txt','.tsv','.csv'):
        p=parse(data)
        if p:occurrences.append(dict(locator=name,encoding='literal',**classify(data,p)))
        elif suffix=='.tm':rejected.append(name)
    elif suffix=='.json':
        try:value=json.loads(data)
        except (UnicodeDecodeError,json.JSONDecodeError) as e:
            json_errors.append(dict(locator=name,error=str(e)));return
        for pointer,d,p in json_candidates(value):
            occurrences.append(dict(locator=name+'::JSON'+pointer,encoding='json',**classify(d,p)))
    elif suffix=='.zip':
        digest=hashlib.sha256(data).hexdigest()
        if digest in archives:
            archives[digest]['duplicates'].append(name);return
        archives[digest]=dict(locator=name,duplicates=[])
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for entry in z.infolist():
                if not entry.is_dir() and Path(entry.filename).suffix.lower() in ('.tm','.txt','.tsv','.csv','.json','.zip'):
                    inspect(name+'::'+entry.filename,z.read(entry))

targets=[ROOT/'Computability/BusyBeaver/Research/PA']
paths=sorted(p for t in targets for p in t.rglob('*') if p.is_file() and p.suffix.lower() in ('.tm','.txt','.tsv','.csv','.json','.zip'))
for i,p in enumerate(paths):
    inspect(str(p.relative_to(ROOT)),p.read_bytes())
for p in sorted(args.incoming.glob('*.zip')):
    inspect('docs/incoming/'+p.name,p.read_bytes())
    paths.append(p)

catalog=list(csv.DictReader((targets[0]/'docs/MACHINES.tsv').open(),delimiter='\t'))
known={r['table_class']:r for r in catalog}
kept_checks=[]
for r in catalog:
    p=ROOT/r['kept_file'];d=p.read_bytes();q=parse(d);a=classify(d,q)
    catalog_count=a['max_reachable'] if a['start'] is None else a['start_reachable']
    good=a['table_class']==r['table_class'] and catalog_count==int(r['states'])
    kept_checks.append(dict(kept_file=r['kept_file'],matches=good,**a))
groups={}
for x in occurrences:
    key=x['table_class']
    if key not in groups:
        groups[key]=dict(table_class=key,states=x['states'],max_reachable=x['max_reachable'],has_spanning_root=x['has_spanning_root'],halt_count=len(x['halt_labels']),locators=[],sha256s=[],in_catalog=key in known)
    g=groups[key];g['locators'].append(x['locator'])
    if x['sha256'] not in g['sha256s']:g['sha256s'].append(x['sha256'])
summary=dict(snapshot='2337ce611a26e308697ccbddb2a1636f989f01c3',files_examined=len(paths),recognized_occurrences=len(occurrences),unique_bytes=len(cache),rootfree_classes=len(groups),graph_spanning_one_halt_classes=sum(g['has_spanning_root'] and g['halt_count']==1 for g in groups.values()),states=sorted(Counter(g['states'] for g in groups.values()).items()),literal_194_classes=len({x['table_class'] for x in occurrences if x['states']==194 and x['encoding']=='literal'}),all_194_classes=len({x['table_class'] for x in occurrences if x['states']==194}),catalog_classes=len(catalog),catalog_recomputed_matches=sum(x['matches'] for x in kept_checks),new_classes=[g for g in groups.values() if not g['in_catalog']],unparsed_tm=rejected,json_parse_failures=json_errors,archives=list(archives.values()),scope=__doc__)
(OUT/'census_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(OUT/'census_occurrences.json').write_text(json.dumps(occurrences,indent=2)+'\n')
(OUT/'census_classes.json').write_text(json.dumps(list(groups.values()),indent=2)+'\n')
(OUT/'catalog_recheck.json').write_text(json.dumps(kept_checks,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ('new_classes','scope','archives','json_parse_failures','unparsed_tm')},indent=2))
print('New classes:',len(summary['new_classes']))
for g in summary['new_classes']:
    print(g['states'],g['table_class'][:16],g['locators'][0])
