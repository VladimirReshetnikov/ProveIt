#!/usr/bin/env python3
"""Independent two-cell proof of the boundary239 split-and-merge rewrite."""
from pathlib import Path
import argparse,hashlib,json,sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Proof checking requires enabled assertions; do not use -O or -OO.')

def parse(path):
    t={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,r=line.split();q,b,w,r=map(int,(q,b,w,r))
        assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b)not in t
        t[q,b]=(w,1 if d=='R' else -1,r)
    states={q for q,_ in t}
    assert len(t)==2*len(states) and all((q,b)in t for q in states for b in (0,1))
    assert {v[2] for v in t.values()}-states=={254}
    return t

def run(t,q,tag,read,count):
    tape={-1:tag,0:read};head=0;trace=[]
    for _ in range(count):
        assert head in tape,'Local block touched unconstrained exterior'
        b=tape[head];w,d,r=t[q,b];trace.append([q,head,b,w,d,r])
        tape[head]=w;head+=d;q=r
    return (q,head,tape),trace

def check(old,new):
    expected={(179,1):(1,-1,215),(187,1):(1,1,179),
      (220,1):(1,1,179),(223,0):(0,1,23),
      (223,1):(1,1,70),(237,0):(0,1,223)}
    removed={(218,0),(218,1)}
    assert set(old)-set(new)==removed and not set(new)-set(old)
    actual={row:new[row] for row in new if old[row]!=new[row]}
    assert actual==expected
    entries={r:sorted((q,b,w,d) for(q,b),(w,d,z)in old.items() if z==r) for r in (179,218,223)}
    assert entries=={179:[(161,0,0,1),(236,0,0,1),(239,0,0,1)],
      218:[(187,1,1,1),(220,1,1,1),(237,0,0,1)],223:[(218,0,0,-1)]}
    rows=[(179,0,0,179,1,1,105),(179,0,1,179,1,5,105),
      (218,0,0,223,3,1,23),(218,0,1,223,1,1,70),
      (218,1,0,179,3,1,105),(218,1,1,179,1,3,70)]
    blocks=[];used=set()
    for q,tag,b,qn,a,z,end in rows:
        c0,p0=run(old,q,tag,b,a);c1,p1=run(new,qn,tag,b,z)
        assert c0==c1==(end,1,{-1:tag,0:b})
        used|={(r[0],r[2])for r in p0+p1}
        blocks.append(dict(old=q,new=qn,left=tag,read=b,old_steps=a,new_steps=z,
          endpoint=end,old_trace=p0,new_trace=p1,entire_tape_unchanged=True))
    return dict(incoming_ports=entries,blocks=blocks,used_rows=sorted(used))

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('old',type=Path)
    ap.add_argument('new',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    t0,t1=parse(a.old),parse(a.new);record=check(t0,t1)
    record.update(status='PASS_INDEPENDENT_BOUNDARY_CONTEXT_SPLIT',old_states=len(t0)//2,
      new_states=len(t1)//2,old_sha256=hashlib.sha256(a.old.read_bytes()).hexdigest(),
      new_sha256=hashlib.sha256(a.new.read_bytes()).hexdigest(),
      checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      proof='The incoming ports force tag zero at old179 and select new179 or new223 when entering old218. Old223 has exactly one incoming port and occurs within old218/read0 blocks. All six cases use only offsets minus1 and zero, preserve the entire tape, and end at an ordinary common state. Ordinary rows agree under the tagged relation; positive blocks therefore give halting equivalence from state95 on every binary initial tape.',
      limitations='Ordinary finite executable certificate, not a proof-assistant kernel theorem.')
    a.output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k not in ('blocks','incoming_ports','used_rows')},indent=2))

if __name__=='__main__':main()
