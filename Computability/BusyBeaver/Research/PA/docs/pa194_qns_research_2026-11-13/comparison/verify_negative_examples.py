#!/usr/bin/env python3
"""Direct blank-tape counterexamples; no compiler or symbolic oracle imported."""
from pathlib import Path
import argparse, hashlib, json

EXAMPLES = [
    ('Rejected CS node1-X','55ef6a8178079348d103ff2001da992dbbad93ba7d2557de97d5975f7176b066'),
    ('Rejected I-tree node1-X','f8abcd947786dd409d208f3cd24ef8de23b1b39e2afd575bf057764253777239'),
    ('Rejected ZR node1-X','1c39a0d81ff342bfd1e68411f17691b0e3b941f16d9c56fea666c51f2d1e81c7'),
]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--tables',type=Path,default=Path(__file__).resolve().parent/'current_census/tables')
    ap.add_argument('--out',type=Path)
    a=ap.parse_args(); results=[]
    for name,digest in EXAMPLES:
        data=(a.tables/(digest+'.tm')).read_bytes()
        assert hashlib.sha256(data).hexdigest()==digest
        rows={}
        for line in data.decode().splitlines():
            if not line.strip() or line.lstrip().startswith('#'):continue
            q,r,w,d,t=line.split();rows[int(q),int(r)]=(int(w),d,int(t))
        q,head,tape=74,0,set()
        for steps in range(10000):
            if q==254: break
            w,d,t=rows[q,int(head in tape)]
            if w:tape.add(head)
            else:tape.discard(head)
            q=t;head+=1 if d=='R' else -1
        assert q==254 and steps==1361
        results.append(dict(name=name,sha256=digest,start=74,halt=254,steps=steps,
                            head=head,one_cells=sorted(tape),observed_halt=True))
    text=json.dumps(results,indent=2)+'\n'
    if a.out:a.out.write_text(text)
    print(text)

if __name__=='__main__':main()
