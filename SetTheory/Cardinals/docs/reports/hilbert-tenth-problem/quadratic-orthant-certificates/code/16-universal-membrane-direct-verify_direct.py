#!/usr/bin/env python3
"""All-input affine loop-body audit and direct literal-register accepting replay."""
from pathlib import Path
from collections import Counter
import json,hashlib
R=Path(__file__).resolve().parent
TM=json.loads((R/'tm_table.json').read_text())
V=json.loads((R/'virtual3.json').read_text());C=json.loads((R/'macro_certificates.json').read_text())
vr=V['rows'];stats=Counter()
assert hashlib.sha256((R/'source/UniversalTM15x2.tm.txt').read_bytes()).hexdigest()=='ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae'
source=(R/'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0].split('_')
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


# Literal whole-register computation, not a macro-count extrapolation.
l=V['entry'];regs=(6,0,0);trace=[];tmcuts=[];z=0
reverse={v:k for k,v in V['tm_cuts'].items()};maximum_population=1+1+sum(x+1 for x in regs)
while l!='HALT':
    if l in reverse and regs[2]==0:tmcuts.append({'step':len(trace),'control':reverse[l],'registers':list(regs)})
    op,i,*dest=vr[l];z+=int(op=='SUB' and regs[i]==0)
    q,new=step(vr,l,regs)
    trace.append({'step':len(trace),'control':l,'registers':list(regs),'next_control':q,'next_registers':list(new)})
    maximum_population=max(maximum_population,1+1+sum(x+1 for x in new))
    l,regs=q,new
    assert len(trace)<10000
assert (len(trace),z,regs,maximum_population)==(328,29,(0,11,0),30)
assert trace[-1]['control']=='tm_I1_1_write' and vr[trace[-1]['control']][0]=='ADD'
assert [(l,row) for l,row in vr.items() if 'HALT' in row[2:]]==[('tm_I1_1_write',['ADD',1,'HALT'])]
tmcuts.append({'step':len(trace),'control':'J1','registers':list(regs)})
# Independently follow the source TM at all eight boundaries.
q='A';b=0;L=6;RR=0
for i,cut in enumerate(tmcuts):
    assert cut['control']==q+str(b) and cut['registers']==[L,RR,0]
    row=TM[q+str(b)]
    if row is None:assert i==7;break
    w,D,q=row
    if D=='R':RR,b=divmod(RR,2);L=2*L+w
    else:L,b=divmod(L,2);RR=2*RR+w
(R/'accepting_counter_trace.json').write_text(json.dumps({'input':{'L':6,'R':0,'T':0},'trace':trace,'final_control':l,'final_registers':list(regs)},indent=2)+'\n')
example={'input':{'L':6,'R':0},'source_TM_steps':7,'register_instructions':len(trace),'failed_SUB_instructions':z,'correct_membrane_steps':3*len(trace)+z,'maximum_boundary_population':maximum_population,'final_registers':list(regs),'tm_cuts':tmcuts,
 'quadratic_ledger':{'natural_witnesses':2811*len(trace),'affine_squares':5*len(trace)+1,'quadratic_products':761*len(trace)},
 'scope':'The complete 328-instruction register trace is enumerated. Separate replays check every membrane step and every quadratic summand.'}
(R/'accepting_example.json').write_text(json.dumps(example,indent=2)+'\n')
stats['complete_accepting_register_instructions']=len(trace);stats['failed_SUB_instructions']=z
from load_input import descriptor
for L,RR in ((0,0),(6,0),(1,7),(2**10000,3**1000)):
    inp=descriptor(L,RR)
    assert inp['expanded_membrane_count']==L+RR+5 and len(inp['motifs'])==5
    assert [x['multiplicity'] for x in inp['motifs'][4]['children']]==[L+1,RR+1,1,1]
    assert inp['generic_motif_positive_edge_coordinates']=={'c:4:0':L,'c:4:1':RR,'c:4:2':0,'c:4:3':0}
    stats['affine_loader_checks']+=1
# Independently reconstruct every membrane rule from the literal register table.
actual=[json.loads(line) for line in (R/'membrane_rules.jsonl').read_text().splitlines()]
assert [z.pop('id') for z in actual]==list(range(len(actual)))
def rulekey(z):return json.dumps(z,sort_keys=True,separators=(',',':'))
expected=set()
def rule(kind,label,symbol,output=(),other=()):
    z={'kind':kind,'label':label,'consume':symbol,'produce':list(output)}
    if kind=='divide':z.update({'other':list(other),'elementary':True})
    expected.add(rulekey(z))
def one(x):return [[x,1]]
for l,row in vr.items():
    op,i,*dest=row;i=str(i+1);u=l+'$1';v=l+'$2'
    if op=='ADD':
        rule('in',i,l,one(l));rule('divide',i,l,one(u),one('t'));rule('out',i,u,one(dest[0]))
    else:
        for h in ('skin','s'):rule('evolve',h,l,[['d',1],['b'+i,1],[u,1]])
        rule('in',i,u,one(u));rule('dissolve',i,u,one(dest[0]));rule('in','s',u,one(v))
        for h in ('skin','s'):rule('out',h,v,one(dest[1]))
for i in ('1','2','3'):
    rule('evolve',i,'t');rule('in',i,'b'+i,one('b'+i));rule('out',i,'b'+i,one('t'))
    for h in ('skin','s',i):rule('evolve',h,'b'+i,one('#'))
    rule('evolve',i,'#',one('#'))
rule('in','s','d',one('t'))
for h in ('skin','s'):
    rule('evolve',h,'t');rule('evolve',h,'d',one('#'));rule('evolve',h,'#',one('#'))
assert len(actual)==len(expected)==2544 and set(map(rulekey,actual))==expected
alpha={z['consume'] for z in actual}|{a for z in actual for k in ('produce','other') for a,n in z.get(k,[])}
assert sorted(alpha)==(R/'object_alphabet.txt').read_text().splitlines() and len(alpha)==1296
assert not any(z['consume']=='HALT' for z in actual)
meta=json.loads((R/'frontend_metadata.json').read_text())
assert meta['counts']=={'registers':3,'instructions':528,'ADD':295,'SUB':233,'membrane_rules':2544,'object_symbols':1296,'labels':5,'semantic_branches':761}
assert meta['rule_kind_counts']==dict(Counter(z['kind'] for z in actual))
stats['literal_membrane_rules_checked']=len(actual);stats['object_symbols_checked']=len(alpha)

receipt={'status':'passed','checks':dict(stats),'scope':'All-input symbolic loop bodies plus finite literal-register replay; original universality is credited to the primary U15,2 table.'}
(R/'register_verification_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
