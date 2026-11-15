#!/usr/bin/env python3
"""Reproduce the literal binary-machine census, using only the standard library.

Usage: python3 census_tables.py --output census INPUT [INPUT ...]
INPUT can be a directory, a .tm file, or a ZIP. ZIPs are recursively inspected.
Arbitrary generators, prose, and JSON-only encodings are intentionally not run.
All tuples are compared exactly; hashes are only stable class identifiers.
"""
from pathlib import Path
import argparse, collections, csv, hashlib, io, json, re, zipfile

def parse(text):
    rows={}
    for raw in text.splitlines():
        line=raw.split('#')[0].strip()
        if not line:continue
        m=re.fullmatch(r'(\S+)\s+([01])\s+([01])\s+([LR])\s+(\S+)',line)
        if not m:return None
        s,b,w,d,t=m.groups();key=(s,int(b))
        if key in rows:return None
        rows[key]=(int(w),1 if d=='R' else -1,t)
    states=sorted({s for s,b in rows});ids={s:i for i,s in enumerate(states)}
    if not states or any((s,b) not in rows for s in states for b in (0,1)):return None
    terminals={t for w,d,t in rows.values()}-set(states)
    if len(terminals)!=1:return None
    return [[(w,d,ids.get(t,-1)) for w,d,t in (rows[s,0],rows[s,1])] for s in states]

def canonical(table):
    """Min exact tuple over spanning roots, tape reflection and bit exchange.

    Terminal-edge actions are erased as an additional structural screen.
    A bit exchange is not asserted to preserve zero-blank semantics.
    """
    n=len(table);best=None
    for flip in (0,1):
        for reflect in (1,-1):
            for root in range(n):
                ids={root:0};q=[root];out=[]
                for s in q:
                    for b in (0,1):
                        w,d,t=table[s][b^flip]
                        if t<0:k=-1;w=0;d=0
                        else:
                            if t not in ids:ids[t]=len(q);q.append(t)
                            k=ids[t];w^=flip;d*=reflect
                        out.extend((w,d,k))
                if len(ids)==n:
                    tup=tuple(out)
                    if best is None or tup<best:best=tup
    return best

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('inputs',nargs='+',type=Path)
    ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--states',type=int,default=194)
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    payloads={};occurrences=[];archives=[];seen_archives=set();errors=[]
    def consume(data,name):
        h=hashlib.sha256(data).hexdigest()
        if name.lower().endswith('.zip'):
            archives.append({'path':name,'sha256':h,'bytes':len(data),'expanded':h not in seen_archives})
            if h in seen_archives:return
            seen_archives.add(h)
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for info in z.infolist():
                    if not info.is_dir() and Path(info.filename).suffix.lower() in ('.zip','.tm'):
                        consume(z.read(info),name+'!'+info.filename)
        elif name.lower().endswith('.tm'):
            if h not in payloads:
                try:table=parse(data.decode('utf-8-sig'))
                except UnicodeError:table=None
                payloads[h]={'bytes':data,'table':table}
                if table is None:errors.append({'path':name,'sha256':h})
            table=payloads[h]['table']
            occurrences.append({'path':name,'sha256':h,'states':None if table is None else len(table)})
    for inp in args.inputs:
        files=sorted(p for p in inp.rglob('*') if p.is_file() and p.suffix.lower() in ('.tm','.zip')) if inp.is_dir() else [inp]
        for p in files:consume(p.read_bytes(),str(p))
    tuples={};classes={};keys={};nonspanning=[]
    for j,(h,p) in enumerate(payloads.items()):
        t=p['table']
        if t is None or len(t)!=args.states:continue
        c=canonical(t)
        if c is None:nonspanning.append(h);continue
        k=hashlib.sha256(repr(c).encode()).hexdigest()
        if k in tuples:assert c==tuples[k]
        else:tuples[k]=c;classes[k]={'class':k,'occurrences':[],'representative_sha256':h}
        keys[h]=k
    for o in occurrences:
        h=o['sha256']
        if h in keys:classes[keys[h]]['occurrences'].append(o)
    summary={'selected_states':args.states,'table_occurrences':len(occurrences),'distinct_table_bytes':len(payloads),'table_parse_errors':len(errors),'selected_occurrences':sum(o['states']==args.states for o in occurrences),'selected_distinct_bytes':sum(p['table'] is not None and len(p['table'])==args.states for p in payloads.values()),'selected_spanning_classes':len(classes),'selected_nonspanning_payloads':len(nonspanning),'distinct_archive_payloads_expanded':len(seen_archives)}
    (args.output/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    (args.output/'census.json').write_text(json.dumps({'summary':summary,'archives':archives,'occurrences':occurrences,'classes':list(classes.values()),'nonspanning_payloads':nonspanning,'parse_errors':errors},indent=2)+'\n')
    reps=args.output/'representatives';reps.mkdir(exist_ok=True)
    for k,v in classes.items():(reps/(k+'.tm')).write_bytes(payloads[v['representative_sha256']]['bytes'])
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
