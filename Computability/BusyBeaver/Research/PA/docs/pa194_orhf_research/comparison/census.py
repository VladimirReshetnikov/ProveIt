#!/usr/bin/env python3
"""Independent, reproducible census of the pinned PA literal machine corpus.

The main census recognizes complete binary five-column tables in TM/TXT/CSV/TSV
files, including nested ZIP members. A supplemental pass recognizes complete
numeric transition maps embedded in JSON. Graph identity is independent of state
names and preserves read, write, and move labels. A start-free identity is
reported only when some state reaches the whole action graph.

This program does NOT prove any machine's consistency calibration or infer a
blank-tape start for native state numbering. It does compute exact action
bisimulation, whose nontrivial classes would permit an unconditional quotient.
"""
from __future__ import annotations
import argparse, collections, csv, hashlib, io, json, re, zipfile
from pathlib import Path

COMMIT = '883da8d55452ea097910ed2509a1eefc833ce292'
TEXT_EXT = {'.tm', '.txt', '.csv', '.tsv'}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def validate(rows, start=None, declared=False):
    if not rows:
        return None
    states = {q for q, _ in rows}
    if len(rows) != 2 * len(states) or any((q,b) not in rows for q in states for b in (0,1)):
        return None
    if any(b not in (0,1) or w not in (0,1) or d not in ('L','R') for (q,b),(w,d,t) in rows.items()):
        return None
    halts = {t for w,d,t in rows.values()} - states
    if len(halts) != 1:
        return None
    if start is None and states == set(range(len(states))):
        start = 0
    if start is not None and start not in states:
        return None
    return rows, states, next(iter(halts)), start, declared

def parse_text(data):
    try:
        text = data.decode('utf-8-sig')
    except UnicodeError:
        return None
    rows, start = {}, None
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith(('#','//',';')):
            m = re.search(r'\bstart\s*[:=]?\s*(\d+)', line, flags=re.I)
            if m and start is None:
                start = int(m.group(1))
            continue
        p = line.split()
        if len(p) != 5 or not p[0].isdigit() or p[1] not in ('0','1') or p[2] not in ('0','1') or p[3] not in ('L','R') or not re.fullmatch(r'-?\d+',p[4]):
            return None
        q,b,w,d,t = int(p[0]),int(p[1]),int(p[2]),p[3],int(p[4])
        if (q,b) in rows:
            return None
        rows[q,b]=(w,d,t)
    return validate(rows,start,start is not None)

def canon(table, root, mirror=False, complement=False):
    rows, states, halt, *_ = table
    labels, queue, ans = {root:0},[root],[]
    for q in queue:
        for b in (0,1):
            w,d,t = rows[q,b ^ int(complement)]
            if complement:
                w ^= 1
            if mirror:
                d = 'R' if d == 'L' else 'L'
            if t == halt:
                target=-1
            else:
                if t not in labels:
                    labels[t]=len(labels)
                    queue.append(t)
                target=labels[t]
            ans.append((w,d,target))
    return sha(json.dumps(ans,separators=(',',':')).encode()), len(queue)

def bisimulation(table):
    rows, states, halt, *_ = table
    labels={q:0 for q in states}; rounds=0
    while True:
        groups={}; new={}
        for q in sorted(states):
            signature=tuple((rows[q,b][0],rows[q,b][1],-1 if rows[q,b][2]==halt else labels[rows[q,b][2]]) for b in (0,1))
            if signature not in groups:
                groups[signature]=len(groups)
            new[q]=groups[signature]
        rounds+=1
        if all(new[q]==labels[q] for q in states):
            break
        labels=new
    blocks=collections.defaultdict(list)
    for q,k in new.items():
        blocks[k].append(q)
    return {'quotient_states':len(blocks),'rounds':rounds,
            'nontrivial_blocks':[v for v in blocks.values() if len(v)>1]}

def analyze(table, include_symmetries=False):
    rows,states,halt,start,declared=table
    roots={q:canon(table,q) for q in states}
    spanning=[h for h,n in roots.values() if n==len(states)]
    r={'states':len(states),'transitions':len(rows),'start':start,
       'start_basis':'comment' if declared else 'dense-zero convention' if start is not None else 'unspecified',
       'halt':halt,'spanning_roots':len(spanning),
       'table_class':min(spanning) if spanning else None,
       'maximum_graph_reachability':max(n for h,n in roots.values()),
       'graph_class':None if start is None else roots[start][0],
       'reachable_from_start':None if start is None else roots[start][1],
       'exact_bisimulation':bisimulation(table)}
    if include_symmetries and len(states)==194 and spanning:
        all_values=[]
        for mirror,complement in ((False,False),(True,False),(False,True),(True,True)):
            vals=[canon(table,q,mirror,complement)[0] for q in states if roots[q][1]==len(states)]
            all_values.append(min(vals))
        r['mirror_class']=min(all_values[:2]); r['symbol_mirror_class']=min(all_values)
    return r

def parse_json_transition(v):
    if not isinstance(v,(list,tuple)) or len(v)!=3:
        return None
    w,d,t=v
    if type(w) is not int or w not in (0,1) or type(t) is not int:
        return None
    if d==1: d='R'
    if d==-1: d='L'
    return (w,d,t) if d in ('L','R') else None

def json_tables(obj,loc='$'):
    rows={}
    if isinstance(obj,dict) and len(obj)>=100:
        for k,v in obj.items():
            m=re.fullmatch(r'\(?\s*(\d+)\s*,\s*([01])\s*\)?',k)
            tr=parse_json_transition(v)
            if m and tr is not None:
                rows[int(m.group(1)),int(m.group(2))]=tr
            else:
                rows={}; break
    elif isinstance(obj,list) and len(obj)>=100:
        for row in obj:
            if not isinstance(row,list) or len(row)!=5 or type(row[0]) is not int or row[1] not in (0,1):
                rows={}; break
            tr=parse_json_transition(row[2:])
            if tr is None or (row[0],row[1]) in rows:
                rows={}; break
            rows[row[0],row[1]]=tr
    table=validate(rows)
    if table is not None and len(table[1])>=100:
        yield loc,table
        return
    if isinstance(obj,dict):
        for k,v in obj.items():
            if isinstance(v,(dict,list)):
                yield from json_tables(v,loc+'.'+k)
    elif isinstance(obj,list):
        for i,v in enumerate(obj):
            if isinstance(v,(dict,list)):
                yield from json_tables(v,loc+'['+str(i)+']')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--json',action='store_true',help='Scan JSON numeric maps as supplemental evidence')
    args=p.parse_args(); repo=args.repo; out=args.out; out.mkdir(parents=True,exist_ok=True)
    roots=[repo/'Computability/BusyBeaver/Research/PA',repo/'docs/incoming']
    occurrences=[]; raws={}; failures=[]; archives=[]; seen_archives=set(); seen_text={}; json_seen=set(); scanned=collections.Counter()
    def add_table(table,name,rawdata,kind):
        key=sha(rawdata)
        occurrences.append({'path':name,'raw_sha256':key,'format':kind})
        if key not in raws:
            raws[key]={'table':table,'first_path':name,'format':kind,'raw':rawdata}
    def visit(data,name,depth=0):
        ext=Path(name).suffix.lower(); scanned[ext]+=1
        if ext=='.zip':
            h=sha(data)
            archives.append({'path':name,'sha256':h,'bytes':len(data),'depth':depth,'repeated':h in seen_archives})
            if h in seen_archives:
                return
            seen_archives.add(h)
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    for info in z.infolist():
                        if info.is_dir():
                            continue
                        e=Path(info.filename).suffix.lower()
                        if e in TEXT_EXT or e=='.zip' or args.json and e=='.json':
                            visit(z.read(info),name+'!'+info.filename,depth+1)
            except zipfile.BadZipFile:
                failures.append({'path':name,'error':'bad zip'})
        elif ext in TEXT_EXT:
            h=sha(data)
            if h in seen_text:
                table=seen_text[h]
            else:
                table=parse_text(data); seen_text[h]=table
            if table:
                add_table(table,name,data,'five-column text')
            elif ext=='.tm':
                failures.append({'path':name,'error':'not a complete binary five-column single-halt table'})
        elif ext=='.json' and args.json:
            h=sha(data)
            if h in json_seen:
                return
            json_seen.add(h)
            try:
                obj=json.loads(data)
            except (ValueError,UnicodeError):
                return
            for loc,table in json_tables(obj):
                canonical='\n'.join(f'{q} {b} {w} {d} {t}' for (q,b),(w,d,t) in sorted(table[0].items())).encode()+b'\n'
                add_table(table,name+'#'+loc,canonical,'JSON numeric transition map')
    paths=sorted(p for root in roots if root.exists() for p in root.rglob('*') if p.is_file() and (p.suffix.lower() in TEXT_EXT|{'.zip'} or args.json and p.suffix.lower()=='.json'))
    for i,path in enumerate(paths):
        visit(path.read_bytes(),str(path.relative_to(repo)))
        if i%1000==0: print('scanned',i,'/',len(paths),flush=True)
    cachefile=out/'analyzed_cache.json'
    cache=json.loads(cachefile.read_text()) if cachefile.exists() else {}
    records=[]
    for i,(h,item) in enumerate(sorted(raws.items())):
        if h not in cache:
            cache[h]=analyze(item['table'])
        records.append(dict(cache[h],raw_sha256=h,first_path=item['first_path'],format=item['format']))
        if i%100==0:
            print('analyzed',i,'/',len(raws),flush=True)
            cachefile.write_text(json.dumps(cache))
    cachefile.write_text(json.dumps(cache))
    by_raw={r['raw_sha256']:r for r in records}
    groups=collections.defaultdict(list)
    for r in records:
        if r['table_class']:
            groups[r['states'],r['table_class']].append(r['raw_sha256'])
    class_records=[]
    for (n,h),members in sorted(groups.items()):
        ps=[x['path'] for x in occurrences if x['raw_sha256'] in members]
        class_records.append({'states':n,'table_class':h,'raw_sha256s':members,'paths':ps})
    reps=out/'representatives194';reps.mkdir(exist_ok=True)
    for r in class_records:
        if r['states']==194:
            (reps/(r['table_class']+'.tm')).write_bytes(raws[r['raw_sha256s'][0]]['raw'])
    for r in records:
        if r['states']==194 and r['table_class'] is None:
            (reps/('unspanned_'+r['raw_sha256']+'.tm')).write_bytes(raws[r['raw_sha256']]['raw'])
    summary={'commit':COMMIT,'scope':'All materialized PA files and incoming ZIPs, recursively; strict literal-table recognizer. JSON transition maps are supplemental when requested. Missing source files are separately listed by the source materializer.',
        'scanned_suffixes':dict(scanned),'recognized_occurrences':len(occurrences),'unique_byte_forms':len(raws),
        'spanning_table_classes':len(groups),'unique_zip_payloads':len(seen_archives),'zip_references':len(archives),
        'classes_by_states':dict(sorted(collections.Counter(n for n,h in groups).items())),
        'unspanned_unique_tables':sum(not r['table_class'] for r in records),
        '193_classes':sum(n==193 for n,h in groups),'194_classes':sum(n==194 for n,h in groups),
        'symmetry_counts':'Not tabulated in this census; exact broader novelty is verified separately by fast_novelty.py.',
        '194_tables_with_nontrivial_exact_bisimulation':sum(r['states']==194 and r['exact_bisimulation']['quotient_states']<194 for r in records),
        '193_tables_with_explicit_start':sum(r['states']==193 and r['start_basis']=='comment' for r in records),
        'recognizer_failures':len(failures),'supplemental_json_tables':sum(r['format'].startswith('JSON') for r in records)}
    for filename,obj in [('summary.json',summary),('census.json',{'summary':summary,'tables':records,'classes':class_records,'occurrences':occurrences,'archives':archives,'failures':failures})]:
        (out/filename).write_text(json.dumps(obj,indent=2)+'\n')
    fields=['path','states','transitions','start','start_basis','halt','reachable_from_start','maximum_graph_reachability','raw_sha256','graph_class','table_class','format','quotient_states']
    with (out/'tables.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader()
        for x in occurrences:
            r=by_raw[x['raw_sha256']]
            w.writerow({k:(x['path'] if k=='path' else r['exact_bisimulation']['quotient_states'] if k=='quotient_states' else r.get(k)) for k in fields})
    (out/'classes194.json').write_text(json.dumps([r for r in class_records if r['states']==194],indent=2)+'\n')
    (out/'classes193.json').write_text(json.dumps([r for r in class_records if r['states']==193],indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
