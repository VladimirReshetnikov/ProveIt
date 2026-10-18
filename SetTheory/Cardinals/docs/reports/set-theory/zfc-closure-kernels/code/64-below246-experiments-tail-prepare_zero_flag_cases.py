from pathlib import Path
import os,sys
root=Path(__file__).resolve().parents[2]
default_base=root/'baseline/context246'
if not default_base.exists():default_base=root/'context246/zfc-context246'
p=Path(os.environ.get('ZFC246_BASE',default_base))
sys.path.insert(0,str(p/'code'))
import check_literal_instructions as L
sites=L.program_sites(p/'sources/Prog254.v')
chosen=[]
for op in ['CI','CD','CB','CC']:
    ss=[s for s in sites if s[1]==op]
    if op in ['CI','CD']:
        for r in range(9):chosen.append(next(s for s in ss if s[2]==r))
    else:chosen.append(ss[0])
firstci=next(s for s in sites if s[1]=='CI')
firstcd=next(s for s in sites if s[1]=='CD')
entries=[(firstci,0,None),(firstcd,0,True),(firstcd,0,False)]
for seed in (0,1,3):
    for s in chosen:
        for pos in ((False,True)if s[1]=='CD'else(None,)):
            entries.append((s,seed,pos))
lines=[]
for (pc,op,r),seed,positive in entries:
    regs=[(i*3+seed)%7 for i in range(9)] if seed else [0]*9
    if op=='CD':regs[L.PHYSICAL[r]]=seed+1 if positive else 0
    spares=[0]if seed==0 else[2,0,3];head=0;span=40+seed
    one=L.paint(pc,span,regs,spares,head)
    target=L.expected(pc,op,r,regs,spares,head,span)
    th,tone,nxt,distance,expected_regs,expected_spares=target
    header=th+distance;primary_end=header+1+sum(v+2 for v in expected_regs)
    lines.append(f'{pc} {op} {r} {seed} {positive} {th} {len(one)} '+ ' '.join(map(str,sorted(one)))+' '+str(len(tone))+' '+' '.join(map(str,sorted(tone)))+f' {header} {primary_end}')
(Path(__file__).resolve().parent/'zero-flag-cases.txt').write_text('\n'.join(lines)+'\n')
print('Cases',len(lines))
