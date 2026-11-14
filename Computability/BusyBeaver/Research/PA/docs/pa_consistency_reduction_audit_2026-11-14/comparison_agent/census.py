#!/usr/bin/env python3
"""Read-only inventory of all incoming archives and literal binary TM tables."""
from pathlib import Path, PurePosixPath
import hashlib, json, re, zipfile, io, argparse
from collections import defaultdict, deque

arguments=argparse.ArgumentParser(description=__doc__)
arguments.add_argument('--repo',type=Path,default=Path(__file__).resolve().parent.parent/'ProveIt')
arguments.add_argument('--out',type=Path,default=Path(__file__).resolve().parent)
options=arguments.parse_args()
ROOT=options.repo.resolve()
OUT=options.out.resolve()
OUT.mkdir(exist_ok=True)
ROW = re.compile(r'^\s*(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)\s*$')
START = re.compile(r'(?im)^\s*(?:#!?\s*)?start\s*[:=]?\s*(\d+)\s*$')

def digest(b): return hashlib.sha256(b).hexdigest()

def parse_table(data):
    try: text = data.decode('utf-8')
    except UnicodeDecodeError: return None
    rows = {}
    for line in text.splitlines():
        m=ROW.match(line)
        if m:
            q,b,w,d,t=m.groups(); key=(int(q),int(b))
            if key in rows: return None
            rows[key]=(int(w),d,int(t))
    states={q for q,b in rows}
    if len(states)<2 or set(rows)!={(q,b) for q in states for b in (0,1)}: return None
    halt=sorted({t for w,d,t in rows.values()}-states)
    sm=START.search(text)
    start=int(sm.group(1)) if sm else (0 if 0 in states else min(states))
    inferred=sm is None
    order={start:0}; queue=deque([start]); canon=[]
    while queue:
        q=queue.popleft()
        if q not in states: continue
        rr=[]
        for b in (0,1):
            w,d,t=rows[q,b]
            if t not in states: nxt='HALT'
            else:
                if t not in order: order[t]=len(order); queue.append(t)
                nxt=order[t]
            rr.append([w,d,nxt])
        canon.append(rr)
    rawcanon=[[q,b,*rows[q,b]] for q,b in sorted(rows)]
    return dict(states=len(states),rows=len(rows),start=start,start_inferred=inferred,
                halt=halt,reachable=len(canon),table_sha256=digest(json.dumps(rawcanon,separators=(',',':')).encode()),
                rooted_graph_sha256=digest(json.dumps(canon,separators=(',',':')).encode()),
                start_provenance='file directive' if sm else 'provisional convention; must validate from documentation')

archives=[]; tables=[]; texts=[]; members=[]; skipped_archives=[]
def process_zip(data, archive, prefix='', depth=0):
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for info in z.infolist():
            if info.is_dir(): continue
            name=prefix+info.filename
            members.append(dict(archive=archive,member=name,size=info.file_size,crc=info.CRC))
            suffix=PurePosixPath(info.filename).suffix.lower()
            if suffix=='.zip':
                if depth<16 and info.file_size<100_000_000:
                    process_zip(z.read(info),archive,name+'!',depth+1)
                else:
                    skipped_archives.append(dict(archive=archive,member=name,size=info.file_size,depth=depth))
                continue
            if suffix not in {'.tm','.txt','.tex','.md','.json','.py','.csv'}: continue
            if info.file_size>20_000_000: continue
            b=z.read(info)
            if suffix in {'.tm','.txt'}:
                parsed=parse_table(b)
                if parsed:
                    tables.append(dict(archive=archive,member=name,sha256=digest(b),**parsed))
            if suffix in {'.tex','.md'} and (suffix=='.tex' or 'readme' in name.lower()):
                try: s=b.decode('utf-8')
                except UnicodeDecodeError: continue
                texts.append(dict(archive=archive,member=name,sha256=digest(b),chars=len(s)))
                safe=OUT/'texts'/Path(archive).stem/Path(*PurePosixPath(name.replace('!','/NESTED/')).parts)
                if '..' not in safe.parts:
                    safe.parent.mkdir(parents=True,exist_ok=True); safe.write_text(s)

for path in sorted((ROOT/'docs/incoming').glob('*.zip')):
    data=path.read_bytes(); before=len(tables); btext=len(texts); bm=len(members)
    process_zip(data,path.name)
    archives.append(dict(archive=path.name,size=len(data),sha256=digest(data),
                         members=len(members)-bm,tables=len(tables)-before,texts=len(texts)-btext))
for path in sorted((ROOT/'Computability/BusyBeaver/Research/PA').rglob('*.tm')):
    data=path.read_bytes(); parsed=parse_table(data)
    if parsed: tables.append(dict(archive='REPOSITORY',member=str(path.relative_to(ROOT)),sha256=digest(data),**parsed))
groups=defaultdict(list)
for i,t in enumerate(tables): groups[t['rooted_graph_sha256']].append(i)
result=dict(snapshot='906367250a7f96c923147b10df392294bced7be5',archives=archives,tables=tables,skipped_archives=skipped_archives,
            graph_groups=dict(groups),texts=texts,
            warning='Graph classes assume start 0 where no directive is present. Native no-0 tables use minimum state provisionally; all inferred starts require provenance review. These whole-corpus graph groups are only provisional indexing aids, not a count of distinct validated designs. Counting and graph isomorphism do not establish halting equivalence.')
(OUT/'inventory.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'members.json').write_text(json.dumps(members,indent=2)+'\n')
print(json.dumps(dict(archives=len(archives),tables=len(tables),graph_classes=len(groups),texts=len(texts),
                     archive_summary=archives),indent=2))
