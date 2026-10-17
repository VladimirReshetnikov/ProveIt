import argparse
from pathlib import Path
from synthesize_local_rows import parse, abstract_windows
p=argparse.ArgumentParser()
p.add_argument('table',type=Path);p.add_argument('output',type=Path)
p.add_argument('--radius',type=int,default=6);p.add_argument('--steps',type=int,default=64)
a=p.parse_args();rows,start,halt,sha=parse(a.table)
assert start==0 and halt==253
w=abstract_windows(rows,start,halt,a.radius)
with a.output.open('w') as f:
    print(253,a.radius,a.steps,file=f)
    for q in range(253):
        for b in (0,1):print(*rows[q,b],file=f)
    for q in range(254):print(len(w[q]),*w[q],file=f)
print(sha,sum(map(len,w.values())))
