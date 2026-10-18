#!/usr/bin/env python3
"""Create exact finite input/output examples for broad contextual merge search."""
from pathlib import Path
import fold_search as f
import check_literal_instructions as lit

def main():
    sites=lit.program_sites(f.BASE/'sources/Prog254.v')
    lines=[str(len(f.OLD))]
    for (q,b),(w,d,t) in sorted(f.OLD.items()):lines.append(f'{q} {b} {w} {1 if d=="R" else -1} {t}')
    cases=[]
    for p,kind,r in sites:
        for positive in ((False,True) if kind=='CD' else (None,)):
            regs=[(i*3+1)%5 for i in range(9)]
            if kind=='CD':regs[lit.PHYSICAL[r]]=2 if positive else 0
            spares=[0,2]
            initial=lit.paint(p,40,regs,spares,0)
            expected=lit.expected(p,kind,r,regs,spares,0,40)
            head=0 if expected is None else expected[0]
            target=[] if expected is None else sorted(expected[1])
            source=sorted(initial)
            cases.append(' '.join(map(str,[int(kind=='CH'),head,len(source),*source,len(target),*target])))
    lines.append(str(len(cases)));lines.extend(cases)
    (f.ROOT/'merge-cases.txt').write_text('\n'.join(lines)+'\n')
    print(len(cases),'cases written')

if __name__=='__main__':main()
