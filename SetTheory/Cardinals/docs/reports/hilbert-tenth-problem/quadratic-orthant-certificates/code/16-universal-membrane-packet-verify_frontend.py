#!/usr/bin/env python3
"""Independent replay of exported literal tables, with symbolic loop-body checks.
The all-input proof is in PROOF.md; affine checks cover every literal instruction.
"""
from pathlib import Path
from collections import Counter
import json,hashlib
R=Path(__file__).resolve().parent
TM=json.loads((R/'tm_table.json').read_text())
V=json.loads((R/'virtual3.json').read_text());P=json.loads((R/'literal2.json').read_text())
C=json.loads((R/'macro_certificates.json').read_text())
vr,pr=V['rows'],P['rows'];stats=Counter()
assert set(V['tm_cuts'])==set(TM)
assert set(P['virtual_cuts'])==set(vr)
assert len(C['tm_macros'])==29 and {c['state'] for c in C['tm_macros']}=={k for k,v in TM.items() if v is not None}
assert len(C['prime_macros'])==len(vr) and {c['virtual_label'] for c in C['prime_macros']}==set(vr)

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

# Validate the source file without importing the generator.
s=(R/'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0]
assert hashlib.sha256((R/'source/UniversalTM15x2.tm.txt').read_bytes()).hexdigest()=='ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae'
for i,word in enumerate(s.split('_')):
    for b in (0,1):
        z=word[b*3:b*3+3];expected=None if z=='---' else [int(z[0]),z[1],z[2]]
        assert TM[chr(65+i)+str(b)]==expected
for rows,n in ((vr,3),(pr,2)):
    for lab,row in rows.items():
        assert row[0] in ('ADD','SUB') and len(row)==(3 if row[0]=='ADD' else 4)
        assert 0<=row[1]<n
        assert all(d in rows or d=='HALT' for d in row[2:])
    assert 'HALT' not in rows

# Independently parse the human-readable literal tables too.
for name,data,regs in [('virtual3',V,['L','R','T']),('literal2',P,['A','B'])]:
    parsed={}
    for line in (R/(name+'.txt')).read_text().splitlines():
        if line.startswith('#'):continue
        label,body=line.split(': ',1);words=body.split()
        if label=='HALT':assert words==['HALT'];continue
        assert label not in parsed
        parsed[label]=[words[0],regs.index(words[1]),*words[2:]]
    assert parsed==data['rows']

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

pcov=set()
for c in C['prime_macros']:
    lab=c['virtual_label'];a=c['prefix'];p=c['prime'];op=c['op']
    assert vr[lab][0]==op and p==(2,3,5)[vr[lab][1]]
    assert c['destinations']==vr[lab][2:]
    dst=[P['virtual_cuts'][d] if d!='HALT' else 'HALT' for d in c['destinations']]
    assert P['virtual_cuts'][lab]==a+('drain' if op=='ADD' else 'rem0')
    if op=='ADD':
        assert_path(pr,a+'drain',(plus(x,1),y),a+'drain',(x,plus(y,p)),p+1,pcov)
        assert_path(pr,a+'drain',(zero,y),a+'restore',(zero,y),1,pcov)
        assert_path(pr,a+'restore',(x,plus(y,1)),a+'restore',(plus(x,1),y),2,pcov)
        assert_path(pr,a+'restore',(x,zero),dst[0],(x,zero),1,pcov)
    else:
        assert_path(pr,a+'rem0',(plus(x,p),y),a+'rem0',(x,plus(y,1)),p+1,pcov)
        assert_path(pr,a+'rem0',(zero,y),a+'quo',(zero,y),1,pcov)
        assert_path(pr,a+'quo',(x,plus(y,1)),a+'quo',(plus(x,1),y),2,pcov)
        assert_path(pr,a+'quo',(x,zero),dst[0],(x,zero),1,pcov)
        for r in range(1,p):
            b=a+'r'+str(r)+'_'
            assert_path(pr,a+'rem0',(aff(r),y),b+'drain',(zero,y),r+1,pcov)
            assert_path(pr,b+'drain',(x,plus(y,1)),b+'drain',(plus(x,p),y),p+1,pcov)
            assert_path(pr,b+'drain',(x,zero),dst[1],(plus(x,r),zero),r+1,pcov)
assert pcov==set(pr),set(pr)-pcov
stats['physical_rows_symbolically_covered']=len(pcov)
assert P['entry']==P['virtual_cuts'][V['entry']]

# Literal, unaccelerated machine interpreters provide additional concrete checks.
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

def check_prime(c,N):
    lab=c['virtual_label'];op=c['op'];p=c['prime'];dst=c['destinations'];Q,r=divmod(N,p)
    target=dst[0] if op=='ADD' or r==0 else dst[1]
    target=P['virtual_cuts'].get(target,target)
    value=p*N if op=='ADD' else Q if r==0 else N
    count=(3*p+1)*N+2 if op=='ADD' else N+3*Q+2 if r==0 else 2*N+2*Q+2
    actual=until(pr,P['virtual_cuts'][lab],(N,0),set(P['virtual_cuts'].values())|{'HALT'},predicate=lambda r:r[1]==0)
    assert actual==(target,(value,0),count),(c,N,actual,(target,value,count))
    stats['concrete_prime_microinstructions']+=actual[2];stats['concrete_prime_cases']+=1
reps={}
for c in C['prime_macros']:reps.setdefault((c['op'],c['prime']),c)
for c in reps.values():
    for N in range(1,257):check_prime(c,N)

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

# End-to-end whole TM instructions through the *literal two-counter table*.
physical_tm_cuts={P['virtual_cuts'].get(v,v) for v in V['tm_cuts'].values()}
for c in C['tm_macros']:
    for L in range(3):
      for RR in range(3):
        initial=[L,RR,0];vlabel,expected,n=until(vr,c['entry'],initial,cuts,predicate=lambda r:r[2]==0)
        plabel=P['virtual_cuts'].get(vlabel,vlabel)
        a=until(pr,P['virtual_cuts'][c['entry']],(2**L*3**RR,0),physical_tm_cuts,predicate=lambda r:r[1]==0 and r[0]%5!=0)
        assert a[0]==plabel and a[1]==(2**expected[0]*3**expected[1],0),(c,L,RR,a,expected)
        stats['concrete_end_to_end_tm_cases']+=1;stats['concrete_end_to_end_microinstructions']+=a[2]

# Initial scratch clearing and prime-to-30 nuisance cofactor preservation.
for L in range(3):
 for RR in range(3):
  for T in range(3):
   for cofactor in (1,7,11):
    N=2**L*3**RR*5**T*cofactor
    a=until(pr,P['entry'],(N,0),{P['virtual_cuts'][V['tm_cuts']['A0']]},predicate=lambda r:r[1]==0)
    assert a[1]==(2**L*3**RR*cofactor,0)
    stats['raw_input_prologue_cases']+=1

# Check all membrane rules independently, including conservative skin-role split.
actual=[json.loads(s) for s in (R/'membrane_rules.jsonl').read_text().splitlines()]
assert [z.pop('id') for z in actual]==list(range(len(actual)))
def key(z):return json.dumps(z,sort_keys=True,separators=(',',':'))
expected=set()
def rule(kind,label,a,out=(),other=()):
    d={'kind':kind,'label':label,'consume':a,'produce':list(out)}
    if kind=='divide':d.update({'other':list(other),'elementary':True})
    expected.add(key(d))
def one(s):return [[s,1]]
for lab,row in pr.items():
    op,i,*d=row;i=str(i+1);u=lab+'$1';v=lab+'$2'
    if op=='ADD':
        rule('in',i,lab,one(lab));rule('divide',i,lab,one(u),one('t'));rule('out',i,u,one(d[0]))
    else:
        for h in ('s','skin'):rule('evolve',h,lab,[['d',1],['b'+i,1],[u,1]])
        rule('in',i,u,one(u));rule('dissolve',i,u,one(d[0]));rule('in','s',u,one(v))
        for h in ('s','skin'):rule('out',h,v,one(d[1]))
for i in ('1','2'):
    rule('evolve',i,'t');rule('in',i,'b'+i,one('b'+i));rule('out',i,'b'+i,one('t'))
    for h in ('s','skin',i):rule('evolve',h,'b'+i,one('#'))
    rule('evolve',i,'#',one('#'))
rule('in','s','d',one('t'))
for h in ('s','skin'):
    rule('evolve',h,'t');rule('evolve',h,'d',one('#'));rule('evolve',h,'#',one('#'))
assert set(map(key,actual))==expected and len(actual)==len(expected)
symbols={z['consume'] for z in actual}|{s for z in actual for k in ('produce','other') for s,n in z.get(k,[])}
assert symbols==set((R/'object_alphabet.txt').read_text().splitlines())
assert not any(z['consume']=='HALT' for z in actual)
assert len(set(vr)|{'HALT'})==len(vr)+1
assert not any('$' in x or x in ('t','d','b1','b2','#') for x in pr)
stats['literal_membrane_rules_checked']=len(actual);stats['literal_object_symbols']=len(symbols)
# Check the executable sparse structural loader on small and very large inputs.
from load_input import descriptor
for A in (1,7,64,2**10000):
    d=descriptor(A);assert d['root']==3 and len(d['motifs'])==4
    assert [m['label'] for m in d['motifs']]==['1','2','s','skin']
    assert d['motifs'][3]['objects']==[[P['entry'],1]]
    assert [e['multiplicity'] for e in d['motifs'][3]['children']]==[A+1,1,1]
    assert d['generic_motif_positive_edge_coordinates']=={'c:3:0':A,'c:3:1':0,'c:3:2':0}
    assert d['expanded_membrane_count']==A+4
    stats['structural_loader_cases']+=1
for bad in (0,-1,1.5,True):
    try:descriptor(bad)
    except ValueError:pass
    else:raise AssertionError(bad)
meta=json.loads((R/'frontend_metadata.json').read_text())
assert meta['counts']=={'tm_defined_rows':29,'virtual_instructions':len(vr),'physical_instructions':len(pr),'membrane_rules':len(actual),'object_symbols':len(symbols),'membrane_labels':4}
assert meta['entry_object']==P['entry']
assert meta['physical_instruction_counts']==dict(Counter(row[0] for row in pr.values()))
assert meta['membrane_rule_counts']==dict(Counter(r['kind'] for r in actual))

receipt={'status':'passed','checks':dict(stats),'scope':'All-input affine loop-body certificates plus proof in PROOF.md; finite direct replay is supplementary, not extrapolated universality or formal verification.'}
(R/'verification_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
