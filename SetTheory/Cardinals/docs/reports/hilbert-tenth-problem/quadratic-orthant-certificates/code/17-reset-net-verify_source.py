#!/usr/bin/env python3
"""All-input affine loop-body audit and direct literal-register accepting replay."""
from pathlib import Path
from collections import Counter
import json,hashlib
R=Path(__file__).resolve().parent/'source'
TM=json.loads((R/'tm_table.json').read_text())
V=json.loads((R/'virtual3.json').read_text());C=json.loads((R/'macro_certificates.json').read_text())
vr=V['rows'];stats=Counter()
assert hashlib.sha256((R/'UniversalTM15x2.tm.txt').read_bytes()).hexdigest()=='ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae'
source=(R/'UniversalTM15x2.tm.txt').read_text().splitlines()[0].split('_')
for q,word in enumerate(source):
    for b in (0,1):
        z=word[b*3:b*3+3]
        assert TM[chr(65+q)+str(b)]==(None if z=='---' else [int(z[0]),z[1],z[2]])
assert set(V['tm_cuts'])==set(TM)
assert len(C['tm_macros'])==29 and {z['state'] for z in C['tm_macros']}=={q for q,v in TM.items() if v is not None}
for l,row in vr.items():
    assert row[0] in ('ADD','SUB') and 0<=row[1]<3 and all(q in vr or q=='HALT' for q in row[2:])
parsed={}
for line in (R/'virtual3.txt').read_text().splitlines():
    if line.startswith('#'):continue
    l,text=line.split(': ',1);row=text.split()
    if l=='HALT':assert row==['HALT'];continue
    parsed[l]=[row[0],['L','R','T'].index(row[1]),*row[2:]]
assert parsed==vr
def aff(c=0,*co):return (c,)+tuple(co)+(0,)*(3-len(co))
def plus(a,c):return (a[0]+c,)+a[1:]
def path(rows,start,regs,stops,cover):
    """Exactly execute an affine straight-line body on all x,y,z>=0.
    Each tested register must be identically 0 or have nonnegative coefficients
    and constant >=1. Stops are checked only after at least one instruction.
    """
    label=start;regs=list(regs);n=0
    while True:
        op,i,*dst=rows[label];cover.add(label);n+=1
        if op=='ADD':regs[i]=plus(regs[i],1);label=dst[0]
        else:
            a=regs[i]
            if a==(0,0,0,0):label=dst[1]
            else:
                assert a[0]>=1 and min(a[1:])>=0,(label,a)
                regs[i]=plus(a,-1);label=dst[0]
        if label in stops:return label,tuple(regs),n
        assert n<100,(start,label)

def assert_path(rows,start,initial,end,final,length,cover):
    actual=path(rows,start,initial,{end},cover)
    assert actual==(end,tuple(final),length),(start,actual,(end,final,length))
    stats['symbolic_paths']+=1

# Every virtual instruction is checked through an unbounded affine loop body,
# a remainder exit, or a constant output tail.
vcov=set();x=aff(0,1);y=aff(0,0,1);z=aff(0,0,0,1);zero=aff()
assert_path(vr,'init_clear_T',(x,y,plus(z,1)),'init_clear_T',(x,y,z),1,vcov)
assert_path(vr,'init_clear_T',(x,y,zero),V['tm_cuts']['A0'],(x,y,zero),1,vcov)
for c in C['tm_macros']:
    a=c['phases_prefix'];X=c['movement_register'];Y=c['other_register'];w=c['write'];qn=c['next_state']
    assert [w,'L' if X==0 else 'R',qn]==TM[c['state']]
    assert V['tm_cuts'][c['state']]==a+'pop0'
    def vec(xx,yy,tt):
        out=[None,None,tt];out[X]=xx;out[Y]=yy;return tuple(out)
    assert_path(vr,a+'pop0',vec(plus(x,2),y,z),a+'pop0',vec(x,y,plus(z,1)),3,vcov)
    for bit in (0,1):
        b=a+str(bit)+'_'
        assert_path(vr,a+'pop0',vec(aff(bit),y,z),b+'back',vec(zero,y,z),1+bit,vcov)
        assert_path(vr,b+'back',vec(x,y,plus(z,1)),b+'back',vec(plus(x,1),y,z),2,vcov)
        assert_path(vr,b+'back',vec(x,y,zero),b+'push',vec(x,y,zero),1,vcov)
        assert_path(vr,b+'push',vec(x,plus(y,1),z),b+'push',vec(x,y,plus(z,2)),3,vcov)
        assert_path(vr,b+'push',vec(x,zero,z),b+'restore',vec(x,zero,z),1,vcov)
        assert_path(vr,b+'restore',vec(x,y,plus(z,1)),b+'restore',vec(x,plus(y,1),z),2,vcov)
        assert_path(vr,b+'restore',vec(x,y,zero),V['tm_cuts'][qn+str(bit)],vec(x,plus(y,w),zero),1+w,vcov)
assert vcov==set(vr),(set(vr)-vcov)
stats['virtual_rows_symbolically_covered']=len(vcov)

def step(rows,lab,regs):
    op,i,*dst=rows[lab];regs=list(regs)
    if op=='ADD':regs[i]+=1;lab=dst[0]
    elif regs[i]>0:regs[i]-=1;lab=dst[0]
    else:lab=dst[1]
    return lab,tuple(regs)
def until(rows,lab,regs,cuts,budget=10_000_000,predicate=lambda regs: True):
    n=0
    while True:
        lab,regs=step(rows,lab,regs);n+=1
        if lab in cuts and predicate(regs):return lab,regs,n
        assert n<budget,(lab,regs,n)

cuts=set(V['tm_cuts'].values())
for c in C['tm_macros']:
    for Q in range(9):
      for Y in range(9):
       for bit in (0,1):
        initial=[0,0,0];initial[c['movement_register']]=2*Q+bit;initial[c['other_register']]=Y
        expected=[0,0,0];expected[c['movement_register']]=Q;expected[c['other_register']]=2*Y+c['write']
        count=5*Q+bit+7*Y+c['write']+4
        a=until(vr,c['entry'],initial,cuts,predicate=lambda r:r[2]==0)
        assert a==(V['tm_cuts'][c['next_state']+str(bit)],tuple(expected),count)
        stats['concrete_tm_virtual_cases']+=1;stats['concrete_tm_virtual_microinstructions']+=a[2]



out={"status":"passed","checks":dict(stats),"scope":"Affine symbolic loop-body checks cover every source row; finite TM macro replays supplement the all-input invariants."}
(R.parent/"source_verification_receipt.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out,indent=2))
