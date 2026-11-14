#!/usr/bin/env python3
"""Audit complete numerical binary transition tables in repository and ZIPs.

The canonical spanning action-graph digest ignores initial state, state labels,
tape reflection and global bit complementation. Non-spanning control graphs are
marked separately and are not claimed to have a canonical isomorphism digest.
"""
import argparse, hashlib, io, json, re, zipfile, subprocess
from collections import Counter, defaultdict, deque
from pathlib import Path

ROW = re.compile(r"^(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)\s*$")

def parse(data):
    try: text = data.decode('utf-8-sig')
    except UnicodeError: return None
    table={}
    for line in text.splitlines():
        line=line.split('#')[0].strip()
        if not line or line.startswith(('//',';')): continue
        m=ROW.fullmatch(line)
        if not m: return None
        s,r,w,d,t=m.groups(); key=(int(s),int(r))
        if key in table: return None
        table[key]=(int(w), d, int(t))
    states=sorted({s for s,r in table})
    if not states or len(table)!=2*len(states): return None
    if any((s,r) not in table for s in states for r in (0,1)): return None
    halts={v[2] for v in table.values()}-set(states)
    if len(halts)>1: return None
    return table,states,next(iter(halts), None)

def serialization(table, states, halt, root, flip=False, reflect=False):
    ids={root:0}; queue=[root]; out=[]
    for s in queue:
        for read in (0,1):
            w,d,t=table[s,read ^ flip]
            if t==halt: idx=len(states)
            else:
                if t not in ids: ids[t]=len(ids);queue.append(t)
                idx=ids[t]
            out.extend((w ^ flip, (d=='R') ^ reflect, idx))
    if len(ids)!=len(states): return None
    return tuple(out)

def digest(obj):
    return hashlib.sha256(json.dumps(obj,separators=(',',':')).encode()).hexdigest()

def canonical(table,states,halt):
    # All possible roots, both tape orientations and both global bit names.
    best=None; roots=0
    for root in states:
        sig=serialization(table,states,halt,root)
        if sig is None: continue
        roots+=1
        for flip in (False,True):
            for reflect in (False,True):
                x=sig if not flip and not reflect else serialization(table,states,halt,root,flip,reflect)
                if best is None or x<best:best=x
    return (digest(best) if best else None), roots

def audit(root,out):
    # A prior result may cache canonical forms; every source is still rescanned.
    occurrences=[]; forms={}; zip_payloads={}; zip_references=[]; skipped=[]
    commit=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD']).decode().strip()
    seen_forms=set()
    if out.exists():
        prior=json.loads(out.read_text())
        if prior.get('commit')==commit:forms=prior['forms']
    def offer(label,data):
        sha=hashlib.sha256(data).hexdigest()
        if sha in forms:
            seen_forms.add(sha)
            occurrences.append({'path':label,'sha256':sha});return
        parsed=parse(data)
        if parsed is None:return
        table,states,halt=parsed
        normalized=[[s,r,*table[s,r]] for s in states for r in (0,1)]
        can,roots=canonical(table,states,halt)
        forms[sha]={'states':len(states),'halt':halt,'min_state':min(states),
                    'transition_digest':digest(normalized),'graph_digest':can,
                    'spanning_roots':roots,'first_path':label}
        seen_forms.add(sha)
        occurrences.append({'path':label,'sha256':sha})
    def scan_zip(label,data,depth=0):
        sha=hashlib.sha256(data).hexdigest()
        zip_references.append({'path':label,'sha256':sha})
        if sha in zip_payloads:return
        zip_payloads[sha]=label
        if depth>20:skipped.append([label,'depth']);return
        try:
            with zipfile.ZipFile(io.BytesIO(data)) as z:
                for name in z.namelist():
                    if name.endswith('/'):continue
                    low=name.lower()
                    if low.endswith('.zip'):scan_zip(label+'!'+name,z.read(name),depth+1)
                    elif low.endswith(('.tm','.txt','.tsv','.csv')):offer(label+'!'+name,z.read(name))
        except (zipfile.BadZipFile,RuntimeError) as ex:skipped.append([label,str(ex)])
    pa=root/'Computability/BusyBeaver/Research/PA'
    for p in sorted(pa.rglob('*')):
        if not p.is_file() or '.git' in p.parts:continue
        if p.suffix.lower() in ('.tm','.txt','.tsv','.csv'):offer(str(p.relative_to(root)),p.read_bytes())
        elif p.suffix.lower()=='.zip':scan_zip(str(p.relative_to(root)),p.read_bytes())
    for p in sorted((root/'docs/incoming').glob('*.zip')):
        scan_zip(str(p.relative_to(root)),p.read_bytes())
    # Sparse checkouts can omit nested archives. Read every omitted relevant
    # tracked object directly from the pinned Git tree, without checkout.
    paths=subprocess.check_output(['git','-C',str(root),'ls-tree','-r','--name-only','HEAD',
        'Computability/BusyBeaver/Research/PA','docs/incoming']).decode().splitlines()
    for name in paths:
        if (root/name).exists():continue
        suffix=Path(name).suffix.lower()
        if suffix not in ('.zip','.tm','.txt','.tsv','.csv'):continue
        data=subprocess.check_output(['git','-C',str(root),'show','HEAD:'+name])
        if suffix=='.zip':scan_zip(name,data)
        else:offer(name,data)
    forms={sha:v for sha,v in forms.items() if sha in seen_forms}
    hist=Counter(v['states'] for v in forms.values())
    report={'commit':commit,
            'scope':'All tracked PA .tm/.txt/.tsv/.csv numeric binary tables and nested ZIPs, plus all current incoming ZIPs; sparse missing files read from Git. Comment-only lines allowed. Exactly two rows per working state, at most one undefined terminal target. Includes the no-halt 4-state synthetic control. Recursive distinct ZIP payloads scanned once. Arbitrary code/JSON/prose encodings are not recognized.',
            'forms':forms,'occurrences':occurrences,
            'zip_payloads':zip_payloads,'zip_references':zip_references,
            'skipped':skipped,'distinct_byte_forms_by_states':dict(sorted(hist.items()))}
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'byte_forms':len(forms),'table_occurrences_in_distinct_zip_payloads_and_files':len(occurrences),'zip_payloads':len(zip_payloads),'zip_references':len(zip_references),'histogram':dict(sorted(hist.items())),'skipped':skipped},indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('root',type=Path);ap.add_argument('output',type=Path)
    a=ap.parse_args();audit(a.root,a.output)
