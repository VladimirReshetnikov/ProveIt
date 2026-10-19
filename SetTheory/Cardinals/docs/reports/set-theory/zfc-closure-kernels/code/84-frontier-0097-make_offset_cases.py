#!/usr/bin/env python3
"""Portable exact finite fixtures for the offset246 runtime search.

A complete program path is required. The original logical program is read
from the maintained public ProveIt checkout or its retained vendored copy.
"""
from pathlib import Path
import argparse,json,hashlib
import literal_reference as lit
ROOT=Path(__file__).resolve().parent

def expected(pc,kind,r,regs,spares):
    regs=regs.copy();spares=spares.copy();head=0;span=40;extra=0
    if kind=='CI':regs[lit.PHYSICAL[r]]+=1;spares.append(0);nxt=lit.add_one(pc)
    elif kind=='CD':
        if regs[lit.PHYSICAL[r]]>1:regs[lit.PHYSICAL[r]]-=1;extra=1;nxt=lit.add_one(pc)
        else:nxt=lit.add_one(lit.remove_to(pc,'0',1))
    elif kind=='CB':nxt=lit.add_one(lit.remove_to(pc,'0',r))
    elif kind=='CC':nxt=lit.remove_to(pc,'1',r)
    else:return None
    head-=nxt is None;span+=extra+(nxt is None)
    return head,lit.paint(nxt or '',span,regs,spares,head)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--program',required=True,type=Path);ap.add_argument('--spares',default='0,2');ap.add_argument('--output',required=True,type=Path);args=ap.parse_args()
    if not __debug__:raise SystemExit('Assertions must remain enabled')
    table=lit.read_table(ROOT/'offset246_old.tm');assert len(table)==492
    lines=[str(len(table))]+[f'{q} {b} {w} {d} {n}' for (q,b),(w,d,n) in sorted(table.items())]
    sites=lit.program_sites(args.program);cases=[]
    spares=list(map(int,args.spares.split(',')));assert spares and min(spares)>=0
    for pc,kind,r in sites:
        for positive in ((False,True) if kind=='CD' else (None,)):
            regs=[1+(i*3+1)%5 for i in range(9)]
            if kind=='CD':regs[lit.PHYSICAL[r]]=3 if positive else 1
            initial=sorted(lit.paint(pc,40,regs,spares,0));answer=expected(pc,kind,r,regs,spares)
            head=0 if answer is None else answer[0];target=[] if answer is None else sorted(answer[1])
            cases.append(' '.join(map(str,[int(kind=='CH'),head,len(initial),*initial,len(target),*target])))
    assert len(cases)==8391
    lines.append(str(len(cases)));lines.extend(cases);args.output.write_text('\n'.join(lines)+'\n')
    print(json.dumps(dict(cases=len(cases),program_sha256=hashlib.sha256(args.program.read_bytes()).hexdigest(),spares=spares,finite_only=True)))
if __name__=='__main__':main()
