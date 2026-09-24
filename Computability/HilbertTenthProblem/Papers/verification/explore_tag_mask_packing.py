"""Exact conditional packing ledgers for the eleven-field tag interface."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_unit_two_ternary_kernel as signed
import explore_parity_free_pell_kernel as free

NAMES='q Q0 Q1 S0 S1 M0 M1 G N Nbar E Ebar Qsum H L cH AH'.split()
SYM=dict(zip(NAMES,sp.symbols(' '.join(NAMES))))
ORDER11=['G','Q0','Q1','S0','S1','M0','M1','N','Nbar','E','Ebar']
TIE_ORDER=['Q0','Q1','N','Nbar','S0','S1','E','Ebar','M0','M1','G']
SPECIAL_ORDER=['G','Qsum','Q0','Q1','S0','S1','N','Nbar','E','Ebar','M0','M1']


def run(ops,env):
    env=dict(env)
    for name,op,left,right in ops:
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a*b if op=='*' else a+b if op=='+' else a-b
    return env


def count(ops):
    return dict(M=sum(o=='*' for _,o,_,_ in ops),A=sum(o!='*' for _,o,_,_ in ops))


def horner(order):
    ops=[];last=order[-1]
    for i,field in enumerate(reversed(order[:-1])):
        p=f'hp{i}';s=f'hs{i}'
        ops.extend([(p,'*','q',last),(s,'+',field,p)]);last=s
    return ops,last


def powers(length):
    out=[('q2','*','q','q'),('q4','*','q2','q2'),('q8','*','q4','q4')]
    if length==12:out.append(('scale','*','q8','q4'))
    else:out.extend([('q10','*','q8','q2'),('scale','*','q10','q')])
    return out


def high_horner(fields):
    ops=[];last=fields[-1]
    for i,f in enumerate(reversed(fields[:-1])):
        p=f'xp{i}';s=f'xs{i}'
        ops.extend([(p,'*','q2',last),(s,'+',f,p)]);last=s
    return ops,last


def paired(special=False):
    high=['Q1','S1','Nbar','Ebar','M1'] if special else ['Q1','Nbar','S1','Ebar','M1']
    ops,X=high_horner(high)
    ops.append(('scaled','*','qm1',X))
    if special:
        ops += [('q2H','*','q2','H'),('low','+','Qsum','q2H'),
                ('q4p1','+','q4',1),('lowbase','*','q4p1','low'),
                ('lengthterm','*','q8','L'),('base','+','lowbase','lengthterm'),
                ('inside','+','scaled','base'),('shifted','*','q2','inside'),
                ('qQs','*','q','Qsum'),('head','+','G','qQs'),('P','+','head','shifted')]
    else:
        ops += [('q2p1','+','q2',1),('base0','*','q2p1','Qsum'),
                ('q2cH','*','q2','cH'),('middle','+','H','q2cH'),
                ('base1','*','q4','middle'),('q2G','*','q2','G'),
                ('upper','+','L','q2G'),('base2','*','q8','upper'),
                ('sum0','+','scaled','base0'),('sum1','+','sum0','base1'),('P','+','sum1','base2')]
    return ops,'P'


def symbolic():
    q=SYM['q'];env=dict(SYM,q2=q*q,q4=q**4,q8=q**8,qm1=q-1)
    substitution={SYM['Qsum']:SYM['Q0']+SYM['Q1'],SYM['H']:SYM['S0']+SYM['S1'],
                  SYM['L']:SYM['M0']+SYM['M1'],SYM['cH']:SYM['E']+SYM['Ebar'],
                  SYM['Nbar']:SYM['Q0']+SYM['Q1']-SYM['N']}
    ops,last=paired();difference=run(ops,env)[last]-sum(SYM[f]*q**i for i,f in enumerate(TIE_ORDER))
    assert sp.expand(difference.subs(substitution,simultaneous=True))==0
    assert len(ops)==20 and count(ops)==dict(M=10,A=10)
    spec,last=paired(True)
    special_sub=dict(substitution)
    special_sub[SYM['Ebar']]=SYM['S0']+SYM['S1']-SYM['E']
    difference=run(spec,env)[last]-sum(SYM[f]*q**i for i,f in enumerate(SPECIAL_ORDER))
    assert sp.expand(difference.subs(special_sub,simultaneous=True))==0
    assert len(spec)==20 and count(spec)==dict(M=10,A=10)
    for length in (11,12):
        assert sp.expand(run(powers(length),dict(q=q))['scale']-q**length)==0
    signed_ops=signed.schedule(1)
    assert len(signed_ops)==43 and count(signed_ops)==dict(M=25,A=18)
    assert len(free.SCHEDULE)==44 and count(free.SCHEDULE)==dict(M=26,A=18)
    results=[]
    for length,core,label in [(11,dict(M=26,A=18),'eleven_fields_parity_free'),
                               (12,dict(M=25,A=18),'twelve_fields_even')]:
        order=ORDER11+(['Qsum'] if length==12 else [])
        raw,_=horner(order);rc=count(raw);pc=count(powers(length))
        total=dict(M=rc['M']+pc['M']+core['M'],A=rc['A']+3+core['A'])
        assert sum(total.values())==72
        results.append(dict(variant=label,raw=rc,powers=pc,index_and_bound=dict(M=0,A=3),kernel=core,total=total,operations=72))
    R,H,v=sp.symbols('R H v')
    geometry=[('qm1','-','q',1),('Rm1','-','R',1),
              ('head_product','*','H','Rm1'),('radix_product','*','R','v')]
    genv=run(geometry,dict(q=q,R=R,H=H,v=v))
    assert sp.expand(genv['head_product']-genv['qm1']-(H*(R-1)-q+1))==0
    assert sp.expand(genv['radix_product']-q-(R*v-q))==0
    assert count(geometry)==dict(M=2,A=2)
    return dict(general_pair_tie=dict(operations=20,histogram=count(ops),order=TIE_ORDER,dag=ops),
                restricted_deletion_two=dict(operations=20,histogram=count(spec),order=SPECIAL_ORDER,dag=spec,
                    powers=4,index_and_bound=3,kernel=43,total=70),
                complete_conditional_ledgers=results,
                index_instructions=[['twiceP','+','P','P'],['index_rhs','+','scale','twiceP'],['bound','+','r','beta']],
                index_comparisons=['existing tr1=index_rhs','bound=scale'],
                geometry=dict(operations=4,histogram=count(geometry),dag=geometry,
                    comparisons=['head_product=qm1','radix_product=q'],
                    shared='R=C*A is already counted by the marker verifier; no q=2J+1 operation is used'),
                safe_component_subtotal=dict(tag=33,mask_power_index_kernel=72,geometry=4,total=109,
                    scope='Before positive-domain adapters and ordinary raw-input conversion.'))


def boolean(n):
    if n<0:return False
    while n:
        n,d=divmod(n,3)
        if d==2:return False
    return True


def split_word(n,mode):
    if mode==0:return 0,n
    if mode==1:return n,0
    a=b=0;p=1;i=0
    while n:
        n,d=divmod(n,3);assert d<2
        if d:
            if i%2:a+=p
            else:b+=p
        p*=3;i+=1
    return a,b


def finite():
    cases=odd_base=even_extra=odd_extra=special_cases=0
    for deletion in (1,2,3,4):
        c=(3**(deletion-1)-1)//2;m=deletion+3;R=3**m;A=R//3
        for t in (1,2,3):
            H=(R**t-1)//(R-1);q=R**t
            tails=list(product(product((0,1),(0,1,m-1)),repeat=t-1))
            for first in (0,1):
                for tail in tails:
                    Q0=Q1=S0=S1=M0=M1=0
                    for row,(sel,p) in enumerate([(first,deletion)]+list(tail)):
                        w=R**row;mark=3**p;interval=(mark-1)//2
                        if sel:Q1+=w*interval;S1+=w;M1+=w*mark
                        else:Q0+=w*interval;S0+=w;M0+=w*mark
                    Qsum=Q0+Q1;L=M0+M1;G=Qsum+A*H
                    for mode in (0,1,2):
                        N,Nbar=split_word(Qsum,mode);E,Ebar=split_word(c*H,mode)
                        env=dict(q=q,qm1=q-1,q2=q*q,q4=q**4,q8=q**8,Q0=Q0,Q1=Q1,S0=S0,S1=S1,
                            M0=M0,M1=M1,G=G,Qsum=Qsum,L=L,H=H,cH=c*H,AH=A*H,N=N,Nbar=Nbar,E=E,Ebar=Ebar)
                        assert all(0<=env[f]<q and boolean(env[f]) for f in ORDER11)
                        assert G%3==1 and 3**deletion<A
                        P=sum(env[f]*q**i for i,f in enumerate(ORDER11))
                        assert P%2==(Qsum+(c+1)*H)%2
                        odd_base+=P%2
                        extra='G' if c%2==0 else 'Qsum'
                        P12=P+q**11*env[extra]
                        assert P12%2==0 and P12%3==1
                        scale=q**12;r=P12+(scale-1)//2
                        assert r%2==0 and r%3==2 and r<scale<r*r
                        assert all(1<=((r//(3**j))%3)<=2 for j in range(12*m*t))
                        if c%2:odd_extra+=1
                        else:even_extra+=1
                        ops,last=paired();expected=sum(env[f]*q**i for i,f in enumerate(TIE_ORDER))
                        assert run(ops,env)[last]==expected
                        if c==1:
                            ops,last=paired(True);expected=sum(env[f]*q**i for i,f in enumerate(SPECIAL_ORDER))
                            assert run(ops,env)[last]==expected and expected%2==0 and expected%3==1
                            special_cases+=1
                        cases+=1
    return dict(cases=cases,odd_eleven_field_packs=odd_base,
                even_c_duplicate_guard_cases=even_extra,odd_c_duplicate_interval_cases=odd_extra,
                restricted_deletion_two_cases=special_cases,
                scope='Exact valid joint-marker word tuples, both c parities, unit conditions, native/even index, and alternative packing identities. These are not complete tag histories or positive-domain compilations.')


def verify():
    return dict(status='PASS_CONDITIONAL_TAG_MASK_PACKING',arithmetic=symbolic(),finite=finite(),
                proof='../1980/EXPLORATION_TAG_MASK_PACKING.md',
                scope='Conditional packing/index ledgers only. Word ranges and nonnegativity are hypotheses; geometry, safe tag relations, positive adapters and ordinary raw input remain separately counted. The20-operation tie is not a lower bound.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
