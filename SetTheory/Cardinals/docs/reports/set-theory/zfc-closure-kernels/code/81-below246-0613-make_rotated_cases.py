from pathlib import Path
import sys,json
import audit245_dense as A
HERE=Path(__file__).parent
cases=[]
gap=int(sys.argv[3]) if len(sys.argv)>3 else 40
if len(sys.argv)>1:
    source=json.loads(Path(sys.argv[1]).read_text());sites=[]
    def walk(n,p):
        e=source['entries'][str(n)]
        if e[0]=='N':walk(e[1],p+'0');walk(e[2],p+'1')
        else:sites.append((p,e[0],e[1]))
    walk(source['root'],'')
else:sites=A.source_sites()
for pc,op,r in sites:
    for positive in ((False,True) if op=='CD' else (None,)):
        regs=[0,1,2,3,5,8,13,21,34]
        if op=='CD':regs[A.PHYSICAL[r]]=17 if positive else 0
        start=A.paint(pc,0,gap,regs,[0]);end=A.desired(pc,op,r,regs,[0],gap)
        initial=[i-A.OFFSET for i,b in enumerate(start) if b]
        if end is None:q=254;h=0;final=[]
        else:q=96;h=end[0];final=[i-A.OFFSET for i,b in enumerate(end[1]) if b]
        row=[len(initial),*initial,q,h,len(final),*final,1,436]
        cases.append((pc,row))
cases.sort(key=lambda c:c[0]!='11101001001010100111000000')
with (Path(sys.argv[2]) if len(sys.argv)>2 else HERE/'rotated_cases.txt').open('w') as f:
    for _,row in cases:print(*row,file=f)
print(len(cases))
