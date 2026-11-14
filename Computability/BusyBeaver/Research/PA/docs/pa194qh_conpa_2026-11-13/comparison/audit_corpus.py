#!/usr/bin/env python3
"""Independent literal-table census, with exact canonical tuples and SHA-256 indexes.

Scans the current PA subtree and incoming ZIPs, including distinct nested ZIP bodies.
This is a syntactic graph census, not a correctness or minimality proof.
"""
from pathlib import Path
import argparse, collections, csv, hashlib, io, json, re, zipfile

ROWS = re.compile(r'^\s*(\d+)\s+(0|1)\s+(0|1)\s+([LR])\s+(\d+)\s*$')

def parse(data):
    try: lines=data.decode('ascii').splitlines()
    except UnicodeDecodeError:return None
    d={}; start=None
    for line in lines:
        if not line.strip():continue
        if line.lstrip().startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',line)
            if m and start is None:start=int(m[1])
            continue
        m=ROWS.fullmatch(line)
        if not m:return None
        q,b,w,dr,n=m.groups(); q,b,w,n=map(int,(q,b,w,n))
        if (q,b) in d:return None
        d[q,b]=(w,dr,n)
    states={q for q,b in d}
    if not states or any((q,b) not in d for q in states for b in (0,1)):return None
    if start is None and sorted(states)==list(range(len(states))):start=0
    if start is not None and start not in states:return None
    halts={n for w,dr,n in d.values()}-states
    return d,states,start,halts

def rooted(d,states,start,mirror=False,complement=False,halt_neutral=False):
    indices={start:0}; order=[start]; out=[]
    for q in order:
        for b0 in (0,1):
            b=b0^complement; w,dr,n=d[q,b]
            w^=complement
            if mirror:dr='L' if dr=='R' else 'R'
            if n in states:
                if n not in indices:indices[n]=len(indices);order.append(n)
                out.append((w,dr,indices[n]))
            else:out.append((0,'R',-1) if halt_neutral else (w,dr,-1))
    return tuple(out),len(order)

def digest(t):return hashlib.sha256(json.dumps(t,separators=(',',':')).encode()).hexdigest()

def analyze(data):
    p=parse(data)
    if p is None:return None
    d,states,start,halts=p
    roots={q:rooted(d,states,q) for q in states}
    most=max(n for t,n in roots.values())
    spanning={q:t for q,(t,n) in roots.items() if n==most}
    # Same definition as upstream machine_classes.py: least HASH, not least tuple.
    table=min(digest(t) for t in spanning.values())
    root_tuple=roots[start][0] if start is not None else None
    return dict(states=len(states),reachable=roots[start][1] if start is not None else most,
        start=start,halt_labels=sorted(halts),table=table,
        machine=digest(root_tuple) if root_tuple is not None else None,
        has_spanning_root=most==len(states),_parsed=p)

def collect(repo,incoming):
    records=[]; payloads={}; archives={}; errors=[]
    def add(where,data,source,packet):
        h=hashlib.sha256(data).hexdigest()
        if h not in payloads:
            p=parse(data)
            if p is None:return
            payloads[h]=data
        records.append(dict(path=where,source=source,packet=packet,sha256=h))
    def scan_zip(where,data,source,packet):
        h=hashlib.sha256(data).hexdigest()
        if h in archives:
            archives[h]['duplicate_occurrences'].append(where);return
        archives[h]=dict(first_path=where,duplicate_occurrences=[],bytes=len(data))
        try:
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for name in sorted(z.namelist()):
                    if name.endswith('/'):continue
                    if name.lower().endswith('.zip'):scan_zip(where+'!'+name,z.read(name),source,packet)
                    elif Path(name).suffix.lower() in ('.tm','.txt','.csv','.tsv'):
                        add(where+'!'+name,z.read(name),source,packet)
        except (zipfile.BadZipFile,RuntimeError) as e: errors.append(dict(path=where,error=str(e)))
    pa=repo/'Computability/BusyBeaver/Research/PA'
    for f in sorted(pa.rglob('*')):
        if not f.is_file():continue
        rel=f.relative_to(repo).as_posix()
        pr=f.relative_to(pa).parts
        packet=pr[1] if len(pr)>1 and pr[0]=='docs' else 'PA/'+pr[0]
        if f.suffix.lower()=='.zip':scan_zip(rel,f.read_bytes(),'filed_nested_zip',packet)
        elif f.suffix.lower() in ('.tm','.txt','.csv','.tsv'):
            add(rel,f.read_bytes(),'filed',packet)
    for f in sorted(incoming.glob('*.zip')):
        scan_zip('docs/incoming/'+f.name,f.read_bytes(),'incoming',f.stem)
    return records,payloads,archives,errors

def write_results(records,facts,archives,errors,out):
    groups=collections.defaultdict(list)
    for r in records:
        x=facts[r['sha256']]
        r.pop('class',None);r.pop('root_resolution',None)
        r.update({k:x[k] for k in ('states','reachable','start','table','machine','has_spanning_root')})
        groups[x['table']].append(r)
    full=[]
    for t,rs in sorted(groups.items()):
        x=facts[rs[0]['sha256']]
        full.append(dict(table_class=t,working_controls=x['states'],max_reachable_controls=max(r['reachable'] for r in rs),has_spanning_root=x['has_spanning_root'],halt_targets=x['halt_labels'],occurrences=len(rs),byte_forms=len(set(r['sha256'] for r in rs)),packets=sorted(set(r['packet'] for r in rs)),sources=sorted(set(r['source'] for r in rs)),representative=min(rs,key=lambda r:('comparison/' in r['path'],len(r['path'])))['path']))
    summary=dict(scope='complete numeric five-column binary tables in the PA subtree and incoming ZIPs; every distinct nested ZIP body scanned once',counts=dict(occurrences=len(records),byte_forms=len(facts),table_classes=len(groups),one_halt_spanning_graph_classes=sum(x['has_spanning_root'] and len(x['halt_targets'])==1 for x in full),diagnostic_table_groups=sum(not x['has_spanning_root'] or len(x['halt_targets'])!=1 for x in full),table_classes_by_working_controls=dict(sorted(collections.Counter(x['working_controls'] for x in full).items())),frontier_194_graph_classes=sum(x['working_controls']==194 for x in full)),archives=archives,errors=errors)
    summary['scope_note']='Some comparison fixtures densely relabel vertices without preserving start0. Structural classes therefore compare all spanning-root traversals; automatically inferred dense starts are diagnostic metadata only. Nonspanning diagnostic fixtures are separately flagged and receive no full-graph isomorphism or consistency claim.'
    cleanfacts={h:{k:v for k,v in x.items() if k not in ('class','root_resolution','resolved_machine','roots','_parsed')} for h,x in facts.items()}
    for name,obj in [('summary.json',summary),('table_classes.json',full),('byte_forms.json',cleanfacts),('occurrences.json',records)]:
        (out/name).write_text(json.dumps(obj,indent=2)+'\n')
    for name,rows in [('table_classes.csv',full),('occurrences.csv',records)]:
        with (out/name).open('w',newline='') as f:
            wr=csv.DictWriter(f,fieldnames=list(rows[0]));wr.writeheader();wr.writerows({k:json.dumps(v) if isinstance(v,(list,dict)) else v for k,v in r.items()} for r in rows)
    print(json.dumps(summary['counts'],indent=2),flush=True)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--incoming',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir(exist_ok=True,parents=True)
    records,payloads,archives,errors=collect(a.repo,a.incoming)
    facts={}
    for i,(h,data) in enumerate(payloads.items()):
        if i%100==0:print('classifying',i,'/',len(payloads),flush=True)
        facts[h]=analyze(data)
    write_results(records,facts,archives,errors,a.out)
if __name__=='__main__':main()
