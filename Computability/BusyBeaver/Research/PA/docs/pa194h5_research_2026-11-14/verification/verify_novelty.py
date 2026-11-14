#!/usr/bin/env python3
"""Exact structural novelty check against the frozen frontier representatives.

The comparison deliberately ignores the designated start and permits state
renaming, global tape reflection, global bit interchange, and arbitrary
effects on transitions into the terminal halt. These equivalences are wider
than blank-zero-tape equivalence. Acceptance proves absence from this literal
corpus only, not independence from unexecuted generators or new mathematics.
Full canonical tuples are compared; digests serve only as result identifiers.
"""
import argparse,hashlib,json
from pathlib import Path

def parse(path):
    rows={}
    for line in path.read_text().splitlines():
        line=line.strip()
        if not line or line.startswith('#'):continue
        parts=line.split()
        if len(parts)!=5:raise ValueError('not a five-column table')
        q,b,w,d,t=parts;q,b,w,t=map(int,(q,b,w,t))
        if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows:
            raise ValueError('invalid or duplicate transition')
        rows[q,b]=(w,d,t)
    states={q for q,b in rows}
    if not states or len(rows)!=2*len(states):raise ValueError('incomplete binary table')
    halts={t for w,d,t in rows.values()}-states
    if len(halts)!=1:raise ValueError('comparison requires exactly one terminal halt')
    return rows,states

def rooted(rows,states,q,reflect,bits):
    order=[q];index={q:0};out=[]
    for state in order:
        for bit in (0,1):
            w,d,t=rows[state,bit^bits]
            if t not in states:
                out.append((0,'R',-1));continue
            if t not in index:index[t]=len(order);order.append(t)
            out.append((w^bits,('L' if d=='R' else 'R') if reflect else d,index[t]))
    return tuple(out) if len(order)==len(states) else None

def canonical(rows,states):
    best=None
    for reflect in (False,True):
        for bits in (False,True):
            for q in states:
                value=rooted(rows,states,q,reflect,bits)
                if value is not None and (best is None or value<best):best=value
    if best is None:raise ValueError('table has no spanning root')
    return best

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('candidate',type=Path)
    p.add_argument('reference_directory',type=Path)
    p.add_argument('--output',type=Path)
    a=p.parse_args();rows,states=parse(a.candidate);value=canonical(rows,states)
    checked=[];matches=[]
    for file in sorted(a.reference_directory.glob('*.tm')):
        rr,ss=parse(file)
        if len(ss)!=len(states):continue
        other=canonical(rr,ss)
        checked.append(file.name)
        if other==value:matches.append(file.name)
    result={'candidate':str(a.candidate),'states':len(states),'transitions':len(rows),
            'reference_count':len(checked),'matches':matches,'structurally_new':not matches,
            'candidate_extended_sha256':hashlib.sha256(json.dumps(value,separators=(',',':')).encode()).hexdigest(),
            'method':'Exact full canonical tuples, every spanning root, reflection, bit interchange, normalized halt effects',
            'scope':'Literal frozen frontier; does not assert a PA calibration or absence from parameterized generators.'}
    print(json.dumps(result,indent=2))
    if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
