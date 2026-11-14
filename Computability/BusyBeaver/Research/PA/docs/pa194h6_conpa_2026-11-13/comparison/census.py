#!/usr/bin/env python3
"""Independent bounded-format census, read-only source inputs."""
from pathlib import Path
import argparse, csv, collections, hashlib, io, json, re, zipfile, sys, subprocess
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--repo',type=Path,required=True,help='Pinned ProveIt checkout')
ap.add_argument('--incoming',type=Path,help='ZIP directory, default REPO/docs/incoming')
ap.add_argument('--output',type=Path,default=Path('census.json'))
ap.add_argument('--states',type=int,help='Optional exact working-state filter')
ap.add_argument('--expected-commit',default='3cc7fbf75ba111a0da696ef2f6001dd528891bd5')
args=ap.parse_args()
commit=subprocess.check_output(['git','-C',str(args.repo),'rev-parse','HEAD'],text=True).strip()
if commit!=args.expected_commit:ap.error('Checkout revision '+commit+' differs from expected '+args.expected_commit)
PA=args.repo/'Computability/BusyBeaver/Research/PA'
INCOMING=args.incoming or args.repo/'docs/incoming'
if not PA.is_dir():ap.error('PA source directory is missing')
if not INCOMING.is_dir():ap.error('Incoming ZIP directory is missing')
ROW=re.compile(r'^\s*(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)\s*$')
START=re.compile(r'\bstart\s*(\d+)',re.I)
def parse(data):
    try: txt=data.decode('ascii')
    except: return
    rows={}; start=None
    for line in txt.splitlines():
        line=line.strip()
        if not line: continue
        if line.startswith('#'):
            m=START.search(line)
            if m and start is None: start=int(m[1])
            continue
        m=ROW.fullmatch(line)
        if not m: return
        q,b,w,d,n=m.groups(); q,b,w,n=map(int,(q,b,w,n))
        if (q,b) in rows: return
        rows[q,b]=w,d,n
    states={q for q,b in rows}
    if not states or len(rows)!=2*len(states): return
    if any((q,b) not in rows for q in states for b in (0,1)): return
    halts={n for w,d,n in rows.values()}-states
    if len(halts)!=1: return
    if start is None and states==set(range(len(states))): start=0
    if start is not None and start not in states: return
    return rows,states,start,next(iter(halts))
def rooted(rows,states,start,mirror=False,swap=False):
    order=[start]; names={start:0}; result=[]
    for q in order:
        for read in range(2):
            w,d,n=rows[q,read ^ swap]
            if swap:w^=1
            if mirror:d='L' if d=='R' else 'R'
            if n in states:
                if n not in names: names[n]=len(order);order.append(n)
                n=names[n]
            else:n=-1
            result.append((w,d,n))
    return hashlib.sha256(json.dumps(result,separators=(',',':')).encode()).hexdigest(),len(order)
records={}; failures=[]; max_archive_depth_observed=0
def add(data,name):
    parsed=parse(data)
    if parsed is None or (args.states is not None and len(parsed[1]) != args.states):return
    sha=hashlib.sha256(data).hexdigest()
    if sha in records:records[sha]['paths'].append(name);return
    rows,states,start,halt=parsed
    rec={'sha256':sha,'states':len(states),'start':start,'halt':halt,'paths':[name]}
    by_root={q:rooted(rows,states,q) for q in states}
    most=max(n for h,n in by_root.values())
    rec['max_reachable']=most
    rec['table_class']=min(h for h,n in by_root.values() if n==most)
    if start is not None:
        rec['machine_class'],rec['reachable']=by_root[start]
    # Use all four action symmetries at every spanning root. Separate from blank equivalence.
    key=[]
    for q,(h,n) in by_root.items():
        if n!=len(states):continue
        key.append(h)
        for mirror,swap in ((1,0),(0,1),(1,1)):
            key.append(rooted(rows,states,q,mirror,swap)[0])
    rec['symmetry_class']=min(key) if key else None
    records[sha]=rec

def scan_zip(data,name,depth=0):
    global max_archive_depth_observed
    max_archive_depth_observed=max(max_archive_depth_observed,depth)
    if depth>32:
        failures.append({"path":name,"error":"Archive nesting exceeds32"});return
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for info in z.infolist():
                if info.is_dir():continue
                suffix=Path(info.filename).suffix.lower()
                if suffix in ('.tm','.txt','.tsv','.csv'):
                    if info.file_size<500_000:add(z.read(info),name+'!'+info.filename)
                elif suffix=='.zip' and info.file_size<100_000_000:
                    scan_zip(z.read(info),name+'!'+info.filename,depth+1)
    except Exception as e: failures.append({'path':name,'error':str(e)})
for f in sorted(PA.rglob('*')):
    if not f.is_file():continue
    suffix=f.suffix.lower()
    if suffix in ('.tm','.txt','.tsv','.csv') and f.stat().st_size<500_000:
        add(f.read_bytes(),'PA/'+str(f.relative_to(PA)))
    elif suffix=='.zip':scan_zip(f.read_bytes(),'PA/'+str(f.relative_to(PA)))
for f in sorted(INCOMING.glob('*.zip')):
    scan_zip(f.read_bytes(),'incoming/'+f.name)
result={'source_commit':commit,'scope':'Existing PA directory and every ZIP in the supplied incoming directory; complete numeric five-column binary L/R tables with exactly one undefined halt label, in .tm,.txt,.tsv,.csv, nested ZIP depth <=32, members <500kB. Source and arbitrary JSON encodings are outside this recognizer. Symmetry class is graph-only; global bit complementation does not preserve blank zero start.','max_archive_depth_observed':max_archive_depth_observed,'incoming_files':[f.name for f in sorted(INCOMING.glob('*.zip'))],'table_count':sum(len(r['paths']) for r in records.values()),'byte_forms':len(records),'records':list(records.values()),'archive_errors':failures}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
print('BY STATES (byte forms):',dict(sorted(collections.Counter(r['states'] for r in records.values()).items())))
print('194 symmetry classes:',len({r['symmetry_class'] for r in records.values() if r['states']==194}))
print('All spanning symmetry classes:',len({r['symmetry_class'] for r in records.values() if r['symmetry_class'] is not None}))
