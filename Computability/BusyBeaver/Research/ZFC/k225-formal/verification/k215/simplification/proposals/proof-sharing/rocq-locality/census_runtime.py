#!/usr/bin/env python3
"""Compare generated runtime proof bodies with only namespace/header normalization."""
from pathlib import Path
import argparse, collections, hashlib, json, re

def drop_header(s):
    s=s.lstrip()
    while s.startswith('(*'):
        level=0;i=0
        while i < len(s):
            if s[i:i+2]=='(*': level+=1;i+=2
            elif s[i:i+2]=='*)':
                level-=1;i+=2
                if level==0: break
            else:i+=1
        if level: raise ValueError('Unclosed leading comment')
        s=s[i:].lstrip()
    return s

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--output',type=Path)
    a=ap.parse_args()
    base=a.repo/'Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq'
    names=['Runtime230Core.v','Tape230Blocks.v','Tape230Carry.v','Interpreter230Sites.v','Sim230.v']
    records=[]
    for name in names:
        groups=collections.defaultdict(list)
        for d in sorted(base.iterdir()):
            p=d/name
            if not p.exists():continue
            s=p.read_text();body=re.sub(r'K\d+F','KCandidate',drop_header(s))
            groups[hashlib.sha256(body.encode()).hexdigest()].append({'candidate':d.name,'bytes':p.stat().st_size,'lines':len(s.splitlines()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
        records.append({'file':name,'normalization':'remove leading comments and whitespace; rename only K<number>F namespaces','groups':[{'normalized_sha256':h,'members':g} for h,g in groups.items()]})
    result=json.dumps(records,indent=2)+'\n'
    if a.output:a.output.write_text(result)
    else:print(result,end='')
if __name__=='__main__':main()
