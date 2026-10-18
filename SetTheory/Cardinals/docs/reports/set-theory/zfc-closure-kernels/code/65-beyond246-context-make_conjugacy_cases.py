#!/usr/bin/env python3
import fold_search as f
import check_literal_instructions as lit

def main():
    sites=lit.program_sites(f.BASE/'sources/Prog254.v')
    lines=[str(len(f.OLD))]
    for (q,b),(w,d,t) in sorted(f.OLD.items()):lines.append(f'{q} {b} {w} {1 if d=="R" else -1} {t}')
    cases=[]
    codes={'CI':0,'CD':1,'CB':2,'CC':3,'CH':4}
    for p,kind,r in sites:
        for positive in ((False,True) if kind=='CD' else (None,)):
            regs=[(i*3+1)%5 for i in range(9)]
            if kind=='CD':regs[lit.PHYSICAL[r]]=2 if positive else 0
            expected=lit.expected(p,kind,r,regs,[0,2],0,40)
            head=0 if expected is None else expected[0]
            nxt='.' if expected is None or not expected[2] else expected[2]
            span=40 if expected is None else expected[3]
            cases.append(f'{codes[kind]} {r if r is not None else -1} {int(bool(positive))} {p} {nxt} {head} {span}')
    lines.append(str(len(cases)));lines.extend(cases)
    (f.ROOT/'conjugacy-cases.txt').write_text('\n'.join(lines)+'\n')
    print(len(cases),'cases')

if __name__=='__main__':main()
