#!/usr/bin/env python3
"""Current-checkout literal-table audit; no external dependencies.

Scope: complete five-column numeric tables in .tm/.txt/.tsv/.csv, and
recursively nested ZIP members. A ZIP payload is scanned once per SHA-256.
The graph key is a full canonical transition tuple, with all spanning
roots tested. Zero-start dense/declared-start keys are recorded separately.
Synthetic graphs without a spanning root remain separate audit entries.
"""
import csv, hashlib, io, json, re, sys, zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = Path(sys.argv[1]).resolve() if len(sys.argv)>1 else ROOT.parent / 'ProveIt'
if not REPO.is_dir():
    raise SystemExit('Usage: python3 -B comparison/census.py /path/to/pinned/ProveIt')
SCAN = [REPO/'Computability/BusyBeaver/Research/PA', REPO/'docs/incoming']
EXT = {'.tm','.txt','.tsv','.csv'}
blobs, zip_payloads, failures = {}, set(), []

def sha(b): return hashlib.sha256(b).hexdigest()

def parse(data):
    try: lines=data.decode('utf-8-sig').splitlines()
    except UnicodeDecodeError: return None
    rows={}; start=None
    for line in lines:
        s=line.strip()
        if not s: continue
        if s.startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',s,re.I)
            if m and start is None: start=int(m.group(1))
            continue
        p=s.split()
        if len(p)!=5: return None
        if not all(p[i].isdigit() for i in (0,1,2,4)): return None
        q,b,w,n=map(int,(p[0],p[1],p[2],p[4])); d=p[3]
        if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows: return None
        rows[q,b]=(w,d,n)
    states={q for q,b in rows}
    if not states or len(rows)!=2*len(states): return None
    halts={n for w,d,n in rows.values()}-states
    if len(halts)!=1: return None
    if start is None and states==set(range(len(states))): start=0
    if start is not None and start not in states: return None
    return rows,states,start

def visit(data,loc,suffix):
    if suffix=='.zip':
        h=sha(data)
        if h in zip_payloads: return
        zip_payloads.add(h)
        try:
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for inf in z.infolist():
                    ext=Path(inf.filename).suffix.lower()
                    if not inf.is_dir() and (ext in EXT or ext=='.zip'):
                        visit(z.read(inf),loc+'!'+inf.filename,ext)
        except zipfile.BadZipFile: failures.append(loc)
        return
    if suffix not in EXT: return
    h=sha(data)
    if h in blobs:
        blobs[h]['locations'].append(loc); return
    obj=parse(data)
    if obj:
        rows,states,start=obj
        blobs[h]={'sha256':h,'locations':[loc],'states':len(states),'start':start,
                  '_rows':rows,'_states':states}

def key_at(rows,states,start,mirror=False,flip=False):
    seen={start:0}; order=[start]; out=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b^flip]
            if mirror: d='R' if d=='L' else 'L'
            w ^= flip
            if n in states:
                if n not in seen: seen[n]=len(seen); order.append(n)
                target=seen[n]
            else: target=-1
            out.append((w,d,target))
    return tuple(out),len(order)

def encode(key): return json.dumps(key,separators=(',',':')).encode()

for folder in SCAN:
    for p in sorted(folder.rglob('*')):
        if p.is_file() and p.suffix.lower() in EXT|{'.zip'}:
            visit(p.read_bytes(),str(p.relative_to(REPO)),p.suffix.lower())
print('parsed',len(blobs),'byte forms',sum(len(x['locations']) for x in blobs.values()),'occurrences',flush=True)

plain_keys={}; symmetry_keys={}
for i,item in enumerate(blobs.values()):
    rows,states=item.pop('_rows'),item.pop('_states')
    roots=[(q,*key_at(rows,states,q)) for q in states]
    spans=[(q,k) for q,k,n in roots if n==len(states)]
    item['spanning_root_count']=len(spans)
    if item['start'] is not None:
        k,n=key_at(rows,states,item['start'])
        item['rooted_class_sha256']=sha(encode(k)); item['reachable']=n
    if spans:
        key=min(k for q,k in spans)
        c=sha(encode(key)); item['root_free_class_sha256']=c
        if c in plain_keys: assert plain_keys[c]==key
        plain_keys[c]=key
        if len(states)==194:
            all_keys=[k for q,k in spans]
            for mirror,flip in ((True,False),(False,True),(True,True)):
                all_keys.extend(key_at(rows,states,q,mirror,flip)[0] for q,k in spans)
            sk=min(all_keys); sc=sha(encode(sk)); item['root_free_symmetry_class_sha256']=sc
            if sc in symmetry_keys: assert symmetry_keys[sc]==sk
            symmetry_keys[sc]=sk
    if (i+1)%100==0: print('classified',i+1,flush=True)

classes={}
for h,x in blobs.items():
    c=x.get('root_free_class_sha256','disconnected:'+h)
    y=classes.setdefault(c,{'class_sha256':c,'states':x['states'],'byte_forms':[], 'locations':[]})
    y['byte_forms'].append(h); y['locations'].extend(x['locations'])
    if 'root_free_symmetry_class_sha256' in x: y['symmetry_class_sha256']=x['root_free_symmetry_class_sha256']

stats={'pinned_commit':'3cc7fbf75ba111a0da696ef2f6001dd528891bd5',
       'literal_occurrences':sum(len(x['locations']) for x in blobs.values()),
       'byte_forms':len(blobs),'root_free_spanning_classes':len(plain_keys),
       'frontier194_classes':sum(x['states']==194 for x in classes.values()),
       'frontier194_symmetry_classes':len(symmetry_keys),'unique_zip_payloads':len(zip_payloads),
       'bad_zip_paths':failures,
       'disconnected_byte_forms':sum(not x['spanning_root_count'] for x in blobs.values())}
out={'statistics':stats,'tables':list(blobs.values()),'classes':list(classes.values())}
(ROOT/'census.json').write_text(json.dumps(out,indent=2)+'\n')
with (ROOT/'frontier194.csv').open('w',newline='') as f:
    w=csv.writer(f); w.writerow(['root_free_class','symmetry_class','byte_forms','occurrences','locations'])
    for x in sorted(classes.values(),key=lambda x:x['class_sha256']):
        if x['states']==194: w.writerow([x['class_sha256'],x['symmetry_class_sha256'],len(x['byte_forms']),len(x['locations']),' | '.join(x['locations'])])
print(json.dumps(stats,indent=2),flush=True)
