import sys, json
from pathlib import Path
BASE=Path('/workspace/scratch/b65d0f102007/sources/context246/zfc-context246')
sys.path.insert(0,str(BASE/'code'))
from check_literal_instructions import *
T=read_table(BASE/'machine/zfc_prefix246_old.tm')
sites=program_sites(BASE/'sources/Prog254.v')
relaxed='--relaxed' in sys.argv
semantic='--semantic' in sys.argv
out=Path(__file__).parent/('cases_semantic.txt' if semantic else ('cases_relaxed.txt' if relaxed else 'cases.txt'))
with out.open('w') as f:
    for pc,kind,r in sites:
        for positive in ((False,True) if kind=='CD' else (None,)):
            regs=[(i*3)%7 for i in range(9)]
            if kind=='CD': regs[PHYSICAL[r]]=1 if positive else 0
            one=paint(pc,40,regs,[0],0)
            target=expected(pc,kind,r,regs,[0],0,40)
            q=96;h=0;used=set();ticks=0;cur=set(one)
            while True:
                ticks+=1; used.add(q*2+int(h in cur))
                w,d,q=T[q,int(h in cur)]
                (cur.add if w else cur.discard)(h);h+=d
                if q==254 or q==96 and target is not None and h==target[0] and cur==target[1]:break
                assert ticks < 10000
            frame_end=target[0]+target[3]+1+sum(v+2 for v in target[4]) if target is not None else 0
            sem=[target[2] or '-',*target[4]] if target is not None else ['-',*regs]
            vals=[len(one),*sorted(one),q,h]+([frame_end] if relaxed else [])+(sem if semantic else [])+[len(cur),*sorted(cur),len(used),*sorted(used)]
            print(' '.join(map(str,vals)),file=f)
print(out,len(sites))
