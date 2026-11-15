#!/usr/bin/env python3
"""Offline exact graph-novelty replay for the current PA194 constructions.

Python3 standard library only. No original repository, network, search run,
or theorem prover is required. Mathematical/physical correctness is outside
this graph comparator's scope. It verifies all frozen table identities and
compares exact canonical tuples, not merely their cryptographic digests.
"""
from pathlib import Path
import argparse, hashlib, json, re

HERE=Path(__file__).resolve().parent

def sha(data):return hashlib.sha256(data).hexdigest()
def encode(value):return json.dumps(value,separators=(',',':')).encode()

def need(test,message):
    if not test:raise ValueError(message)

def parse(data):
    rows={};declared=None
    for line in data.decode('ascii').splitlines():
        line=line.strip()
        if not line:continue
        if line.startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',line)
            if m and declared is None:declared=int(m.group(1))
            continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        need(b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows,'Invalid row')
        rows[q,b]=w,d,n
    states=sorted({q for q,b in rows});ss=set(states)
    need(len(states)==194 and set(rows)=={(q,b) for q in states for b in (0,1)},'Not a complete194-state binary table')
    need(len({n for w,d,n in rows.values()}-ss)==1,'Not one external halt')
    start=declared if declared is not None else (0 if states==list(range(194)) else None)
    need(start is None or start in ss,'Invalid declared start')
    return rows,states,start

def canonical(rows,states,mirror=False,flip=False,loose=False):
    """Least spanning-root tuple; prune only lexicographically losing prefixes."""
    ss=set(states);count=len(states);best=None
    for start in states:
        index={start:0};order=[start];out=[];relation=0;rejected=False
        for q in order:
            for b in (0,1):
                w,d,n=rows[q,b^flip];w^=flip
                if mirror:d='L' if d=='R' else 'R'
                if n in ss:
                    if n not in index:index[n]=len(index);order.append(n)
                    item=(w,d,index[n])
                else:item=(0,'R',-1) if loose else (w,d,-1)
                if best is not None and relation==0:
                    k=len(out)
                    if item>best[k]:rejected=True;break
                    if item<best[k]:relation=-1
                out.append(item)
            if rejected:break
        if not rejected and len(order)==count:
            candidate=tuple(out)
            if best is None or candidate<best:best=candidate
    return best

def strong(rows,states):
    values=[canonical(rows,states,mirror=m,flip=f,loose=True)
            for m in (False,True) for f in (False,True)]
    need(all(x is not None for x in values),'Nonspanning graph')
    return min(values)

def reachable(rows,states,start):
    ss=set(states);seen={start};pending=[start]
    for q in pending:
        for b in (0,1):
            n=rows[q,b][2]
            if n in ss and n not in seen:seen.add(n);pending.append(n)
    return len(seen)

def bisimulation_count(rows,states):
    ss=set(states);blocks={q:0 for q in states}
    while True:
        signatures={q:tuple((w,d,blocks[n] if n in ss else -1)
                           for b in (0,1) for w,d,n in [rows[q,b]]) for q in states}
        ids={v:i for i,v in enumerate(sorted(set(signatures.values())))}
        new={q:ids[signatures[q]] for q in states}
        if len(set(new.values()))==len(set(blocks.values())):return len(ids)
        blocks=new

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);a=ap.parse_args()
    manifest=json.loads((HERE/'manifest.json').read_text())
    classes=json.loads((HERE/'classes194.json').read_text())
    need(len(classes)==manifest['reference_count']==528,'Incorrect reference count')
    for name,digest in manifest['sha256'].items():
        need(sha((HERE/name).read_bytes())==digest,'Changed file: '+name)
    refs=[]
    for key,metadata in sorted(classes.items()):
        rows,states,start=parse((HERE/'tables'/(key+'.tm')).read_bytes())
        plain=canonical(rows,states);enlarged=strong(rows,states)
        need(plain is not None and sha(encode(plain))==key,'Incorrect ordinary canonical class: '+key)
        need(sha(encode(enlarged))==metadata['strong_class'],'Incorrect enlarged canonical class: '+key)
        need(bisimulation_count(rows,states)==194,'A reference has an ordinary state quotient: '+key)
        refs.append((key,plain,enlarged))
    candidates=[];previous=[]
    for name in manifest['candidate_names']:
        path=HERE/'candidates'/(name+'.tm');data=path.read_bytes();rows,states,start=parse(data)
        need(start==0 and reachable(rows,states,start)==194,'Candidate start is not spanning')
        plain=canonical(rows,states);enlarged=strong(rows,states)
        prior=[k for k,c,s in refs if plain==c or enlarged==s]
        peer=[k for k,c,s in previous if plain==c or enlarged==s]
        need(not prior and not peer,'Candidate has a cosmetic match: '+name)
        candidates.append({'name':name,'sha256':sha(data),'states':194,'rows':388,'start':0,
                           'start_reachable':194,'canonical_sha256':sha(encode(plain)),
                           'strong_sha256':sha(encode(enlarged)),'prior_matches':prior,'new_peer_matches':peer})
        previous.append((name,plain,enlarged))
    result={'source_commit':manifest['source_commit'],'reference_194_classes':len(refs),
            'verified_manifest_table_files':len(manifest['sha256']),
            'comparison':'Exact canonical tuples, arbitrary spanning root and control names, mirror, global symbol exchange and ignored halt-edge actions.',
            'all_reference_bisimulation_counts':194,'candidates':candidates,'passed':True,
            'scope':'Graph novelty and finite state-quotient screen only. Does not establish machine correctness or consistency calibration. Global symbol exchange is not asserted to preserve the fixed-zero-blank semantics.'}
    text=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
