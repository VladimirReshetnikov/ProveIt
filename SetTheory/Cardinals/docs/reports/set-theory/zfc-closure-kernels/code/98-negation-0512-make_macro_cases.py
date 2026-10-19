#!/usr/bin/env python3
"""Independent finite fixtures for the three arithmetic microcode contracts.

Local cases are discovery filters; they are not a universal proof. Input table
is passed explicitly. Every case specifies the entire finite one support.
"""
import argparse,json,hashlib
from pathlib import Path

def B(values):
    return ''.join('0'+'1'*(v+1) for v in values)

def main():
    p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('output',type=Path);p.add_argument('--append',type=int,default=1,help='Appended spare value; -1 means no new block');a=p.parse_args()
    rows=[]
    for line in a.table.read_text().splitlines():
        if not line.startswith('#'):
            q,b,w,d,t=line.split();rows.append((int(q),int(b),int(w),1 if d=='R' else -1,int(t)))
    cases=[]
    for prefix in ([],[0],[1],[3],[0,1],[3,0,2]):
        for x in (0,1,3,7):
            for suffix in ([1],[0],[0,2],[2,0,3]):
                left='1010011';start=B(prefix)+'00'+'1'*x+B(suffix)
                finish=B(prefix)+B([x+1])+B(suffix)+(B([a.append]) if a.append>=0 else '')
                cases.append(dict(kind='increment',start=73,finish=48,head=-1,before=start,after=finish,left=left))
                start=B(prefix)+'00'+'1'*(x+1)+B(suffix)
                finish='1'+B(prefix)+B([x])+B(suffix)
                cases.append(dict(kind='positive_decrement',start=95,finish=48,head=0,before=start,after=finish,left=left))
            start=B(prefix)+'00'+B([x,1])
            finish=B(prefix)+B([0,x,1])
            cases.append(dict(kind='zero_decrement',start=95,finish=112,head=-1,before=start,after=finish,left='1010011'))
    out=[str(len(rows))]+[' '.join(map(str,r)) for r in rows]+[str(len(cases))]
    for c in cases:
        def ones(word):
            return [i-len(c['left']) for i,b in enumerate(c['left']+word) if b=='1']
        initial=ones(c['before']);target=ones(c['after'])
        out.append(' '.join(map(str,[c['start'],c['finish'],c['head'],len(initial),*initial,len(target),*target])))
    a.output.write_text('\n'.join(out)+'\n')
    a.output.with_suffix('.json').write_text(json.dumps(dict(cases=cases,table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest()),indent=2)+'\n')
    print(json.dumps(dict(cases=len(cases),output=str(a.output))))

if __name__=='__main__':main()
