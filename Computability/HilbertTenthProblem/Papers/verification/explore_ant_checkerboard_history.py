#!/usr/bin/env python3
"""Counted bounded Langton-ant history, not a raw-input universal compiler."""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import random
import sympy as sp

import explore_base_three_pell_kernel as kernel
from round13_1980_certificate import verify_primitives
import round4_1980_operation_count as baseline

PARAMETERS = ['InitialMemoryPlus', 'FinalMemoryPlus', 'InitialHead',
              'FinalHead', 'FinalSignPlus']
RAW = ['A','B','GE','GW','GN','GS','D','E','F','G','Z','SW','SN']
GEO = ['q','Q','W','uQ','uW','Gt','Gy','WidthOdd','HeightEven',
       'K','Wp','HeadRoot','HeadQuot']
UNIQUE_FIELDS = ['A','B','C','D','E','F','G','GE','GW','GN','GS',
                 'TestE','TestW','TestN','TestS']
FIELDS = UNIQUE_FIELDS + ['D']
NAMES = PARAMETERS + [x+'Plus' for x in RAW] + GEO + [
    'Bound'+x for x in UNIQUE_FIELDS+['Z']] + ['BoundInitial','BoundHead'] + kernel.CORE_NAMES
SYM = {name: sp.Symbol(name) for name in NAMES}


def build():
    ops=[]; tests=[]; source=[]; groups=Counter(); z=SYM
    def op(name,kind,a,b,group):
        ops.append((name,kind,a,b));groups[group]+=1;return name
    def eq(a,b,residual):tests.append((a,b));source.append(residual)
    raw={x:z[x+'Plus']-1 for x in RAW}
    for x in RAW:op(x,'-',x+'Plus',1,'positive adapters')
    for x,par in [('I','InitialMemoryPlus'),('FM','FinalMemoryPlus'),('FZ','FinalSignPlus')]:
        op(x,'-',par,1,'positive adapters')
    I,FM,FZ=[z[x]-1 for x in ['InitialMemoryPlus','FinalMemoryPlus','FinalSignPlus']]
    q,Q,W=[z[x] for x in ['q','Q','W']]
    Gt,Gy,K,Wp=[z[x] for x in ['Gt','Gy','K','Wp']]
    # Every radix and extent is recovered from these positive equations.
    op('q_product','*','Q','uQ','geometry');eq('q','q_product',q-Q*z['uQ'])
    op('Q_product','*','W','uW','geometry');eq('Q','Q_product',Q-W*z['uW'])
    for x in ['q','Q','W']:op(x+'m1','-',x,1,'geometry')
    op('time_repunit','*','Gt','Qm1','geometry');eq('qm1','time_repunit',q-1-Gt*(Q-1))
    op('row_repunit','*','Gy','Wm1','geometry');eq('Qm1','row_repunit',Q-1-Gy*(W-1))
    op('width8','*',8,'WidthOdd','checkerboard geometry')
    op('width_rhs','+','width8',3,'checkerboard geometry');eq('W','width_rhs',W-8*z['WidthOdd']-3)
    op('Wplus','+','W',1,'checkerboard geometry')
    op('height_even','*','Wplus','HeightEven','checkerboard geometry')
    eq('Gy','height_even',Gy-(W+1)*z['HeightEven'])
    op('checker8','*',8,'K','checkerboard geometry');eq('qm1','checker8',q-1-8*K)
    op('Odd','*',3,'K','checkerboard geometry')
    op('last_column','*',3,'Wp','checkerboard geometry');eq('W','last_column',W-3*Wp)
    op('VH','*','Gt','HeightEven','checkerboard geometry')
    op('Eedge','*','Wp','VH','checkerboard geometry')
    op('Nedge','*','Gt','WidthOdd','checkerboard geometry')
    op('Sbase3','*',3,'Nedge','checkerboard geometry')
    op('Sbase','+','Sbase3','Gt','checkerboard geometry')
    op('Sedge','*','uW','Sbase','checkerboard geometry')
    for d,edge,wrong in [('E','Eedge','Odd'),('W','VH','Odd'),('N','Nedge','K'),('S','Sedge','K')]:
        op('Forbidden'+d,'+',wrong,edge,'checkerboard geometry')
        op('Test'+d,'+','G'+d,'Forbidden'+d,'edge tests')
    op('initial_bound','+','I','BoundInitial','initial interface');eq('initial_bound','Q',I+z['BoundInitial']-Q)
    op('head_bound','+','InitialHead','BoundHead','initial interface');eq('head_bound','Q',z['InitialHead']+z['BoundHead']-Q)
    op('head_divisor','*','InitialHead','HeadQuot','initial interface');eq('q','head_divisor',q-z['InitialHead']*z['HeadQuot'])
    op('head_square','*','HeadRoot','HeadRoot','initial interface');eq('InitialHead','head_square',z['InitialHead']-z['HeadRoot']**2)
    # Four direction fields also encode the provisional output sign.
    op('Ce','+','GE','GW','local and head sums')
    op('Co','+','GN','GS','local and head sums')
    op('C','+','Ce','Co','local and head sums')
    op('Zprime','+','GW','GN','local and head sums')
    C=sum(raw[x] for x in ['GE','GW','GN','GS']);Zp=raw['GW']+raw['GN']
    op('DE','+','D','E','local and head sums');eq('C','DE',C-raw['D']-raw['E'])
    op('AE','+','A','E','local and head sums');op('BD','+','B','D','local and head sums')
    eq('AE','BD',raw['A']+raw['E']-raw['B']-raw['D'])
    op('FG','+','F','G','local and head sums');eq('D','FG',raw['D']-raw['F']-raw['G'])
    op('ZG','+','Z','G','local and head sums');op('ZpF','+','Zprime','F','local and head sums')
    eq('ZG','ZpF',raw['Z']+raw['G']-Zp-raw['F'])
    op('SE','*',3,'GE','spatial shifts')
    op('west_lhs','*',3,'SW','spatial shifts');eq('west_lhs','GW',3*raw['SW']-raw['GW'])
    op('SS','*','W','GS','spatial shifts')
    op('north_lhs','*','W','SN','spatial shifts');eq('north_lhs','GN',W*raw['SN']-raw['GN'])
    op('NextEW','+','SE','SW','local and head sums');op('NextNS','+','SN','SS','local and head sums')
    op('NextC','+','NextEW','NextNS','local and head sums')
    op('NextZ','+','SW','SS','local and head sums')
    NC=3*raw['GE']+raw['SW']+raw['SN']+W*raw['GS'];NZ=raw['SW']+W*raw['GS']
    op('qFC','*','q','FinalHead','head time');op('QNC','*','Q','NextC','head time')
    op('head_lhs','+','C','qFC','head time');op('head_rhs','+','InitialHead','QNC','head time')
    eq('head_lhs','head_rhs',C+q*z['FinalHead']-z['InitialHead']-Q*NC)
    op('qFZ','*','q','FZ','head time');op('QNZ','*','Q','NextZ','head time')
    op('sign_lhs','+','Z','qFZ','head time');eq('sign_lhs','QNZ',raw['Z']+q*FZ-Q*NZ)
    op('qFM','*','q','FM','memory time');op('QB','*','Q','B','memory time')
    op('memory_lhs','+','A','qFM','memory time');op('memory_rhs','+','I','QB','memory time')
    eq('memory_lhs','memory_rhs',raw['A']+q*FM-I-Q*raw['B'])
    forbidden={
        'E':3*K+Wp*Gt*z['HeightEven'],
        'W':3*K+Gt*z['HeightEven'],
        'N':K+Gt*z['WidthOdd'],
        'S':K+z['uW']*(3*Gt*z['WidthOdd']+Gt)}
    values=dict(raw,C=C,**{'Test'+d:raw['G'+d]+forbidden[d] for d in 'EWNS'})
    for field in UNIQUE_FIELDS+['Z']:
        lhs=op('range_'+field,'+',field,'Bound'+field,'field bounds')
        eq(lhs,'q',values[field]+z['Bound'+field]-q)
    # Sixteen fields; D is repeated to obtain even parity without an adapter.
    previous=FIELDS[-1]
    for index,field in enumerate(reversed(FIELDS[:-1])):
        mul=op('pack_mul_'+str(index),'*','q',previous,'packing')
        previous=op('pack_add_'+str(index),'+',field,mul,'packing')
    P=sum(values[x]*q**i for i,x in enumerate(FIELDS))
    for name,left,right in [('q2','q','q'),('q4','q2','q2'),('q8','q4','q4'),('L','q8','q8')]:
        op(name,'*',left,right,'mask and Pell')
    op('n2','*',9,'L','mask and Pell');op('pP','*',3,previous,'mask and Pell')
    op('gap','-','n2','pP','mask and Pell');op('r_rhs','-','gap',1,'mask and Pell')
    ops.extend(kernel.CORE);groups['mask and Pell']+=len(kernel.CORE)
    core_sub={kernel.SYM['q']:q**4,kernel.SYM['P0']:P}
    core_sub.update({kernel.SYM[x]:z[x] for x in kernel.CORE_NAMES})
    tests.extend(kernel.EQUALITIES)
    source.extend(p.subs(core_sub,simultaneous=True) for p in kernel.source_residuals())
    return ops,tests,source,groups


def certificate():
    ops,tests,source,groups=build();env=dict(SYM)
    histogram=baseline.run_schedule(ops,env)
    correction=source[-3]*((2*SYM['r']+1+SYM['j']*SYM['c'])**2-SYM['y_aux']**2)
    records=[]
    for index,((left,right),residual) in enumerate(zip(tests,source)):
        extra=correction if index==len(source)-2 else sp.Integer(0)
        assert sp.expand(env[left]-env[right]-residual-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(residual)))
    primitives,counts=verify_primitives(ops,env)
    assert len(ops)==len(primitives)==sum(groups.values())==174,(len(ops),groups)
    assert len(tests)==len(source)
    return dict(operations=len(ops),histogram=histogram,primitive_histogram=counts,
                groups=dict(groups),parameters=PARAMETERS,
                positive_unknowns=[x for x in NAMES if x not in PARAMETERS],
                equations=len(tests),instructions=primitives,residuals=records)


def word(values):return sum(value*3**i for i,value in enumerate(values))
def boolean(value,length):
    for _ in range(length):
        value,digit=divmod(value,3)
        if digit>1:return False
    return value==0


def geometry(width,height,times):
    W=3**width;Q=W**height;q=Q**times
    Gt=(q-1)//(Q-1);Gy=(Q-1)//(W-1)
    v=(Q-1)//(W*W-1);uW=Q//W;wp=W//3;wo=(W-3)//8;K=(q-1)//8
    masks={'E':3*K+wp*Gt*v,'W':3*K+Gt*v,
           'N':K+Gt*wo,'S':K+uW*(3*Gt*wo+Gt)}
    for d in 'EWNS':
        expected=[]
        for _ in range(times):
            for yy in range(height):
                for xx in range(width):
                    black=(xx+yy)%2==0
                    wrong=(not black) if d in 'EW' else black
                    edge={'E':xx==width-1,'W':xx==0,'N':yy==0,'S':yy==height-1}[d]
                    expected.append(int(wrong or edge))
        assert masks[d]==word(expected)
    return W,Q,q,masks


def central_valuation(r):
    answer=0
    while r:
        # The factorial formula is independent of the Boolean-word checker.
        r2=r*2
        while r:
            r//=3;r2//=3;answer+=r2-2*r
        break
    return answer


def one_case(width,height,initial,start,steps):
    board=list(initial);position=start;direction=0 # N,E,S,W
    cell_count=width*height
    columns={x:[] for x in ['A','B','C','D','E','F','G','Z','GE','GW','GN','GS']}
    for _ in range(steps):
        xx,yy=position%width,position//width;black=(xx+yy)%2==0
        assert (direction%2==0)==black
        sign=direction//2
        old=board[position];out=(direction+(1 if old==0 else -1))%4
        provisional=sign^old
        route=['N','E','S','W'][out]
        delta={'E':1,'W':-1,'N':-width,'S':width}[route]
        nx,ny=xx+{'E':1,'W':-1}.get(route,0),yy+{'N':-1,'S':1}.get(route,0)
        if not(0<=nx<width and 0<=ny<height):return None
        rows={x:[0]*cell_count for x in columns};rows['A']=board.copy()
        rows['C'][position]=1;rows['Z'][position]=sign
        rows['D'][position]=old;rows['E'][position]=1-old
        rows['F'][position]=sign*old;rows['G'][position]=(1-sign)*old
        rows['G'+route][position]=1
        board[position]^=1;rows['B']=board.copy()
        for x in columns:columns[x].extend(rows[x])
        assert provisional==int(route in 'WN')
        position+=delta;direction=out
    W,Q,q,forbidden=geometry(width,height,steps)
    z={x:word(values) for x,values in columns.items()}
    for d in 'EWNS':z['Test'+d]=z['G'+d]+forbidden[d]
    assert all(boolean(z[x],cell_count*steps) and 0<=z[x]<q for x in UNIQUE_FIELDS+['Z'])
    assert z['C']==z['GE']+z['GW']+z['GN']+z['GS']==z['D']+z['E']
    assert z['A']+z['E']==z['B']+z['D']
    assert z['D']==z['F']+z['G']
    assert z['Z']+z['G']==z['GW']+z['GN']+z['F']
    assert z['GW']%3==z['GN']%W==0
    shifted=[3*z['GE'],z['GW']//3,z['GN']//W,W*z['GS']]
    nc=sum(shifted);nz=shifted[1]+shifted[3]
    initial_head=3**start;final_head=3**position;final_sign=(direction//2)*final_head
    assert z['C']+q*final_head==initial_head+Q*nc
    assert z['Z']+q*final_sign==Q*nz
    assert z['A']+q*word(board)==word(initial)+Q*z['B']
    P=sum(z[x]*q**i for i,x in enumerate(FIELDS))
    assert P<q**16 and P%2==0 and boolean(P,16*cell_count*steps)
    r=9*q**16-3*P-1
    assert r%2==0 and central_valuation(r)==16*cell_count*steps+2
    assert all(z[x]+(q-z[x])==q and q-z[x]>0 for x in UNIQUE_FIELDS+['Z'])
    return dict(width=width,height=height,steps=steps,start=start,end=position,
                old_word=str(word(initial)),new_word=str(word(board)),r_bit_length=r.bit_length())


def regression():
    geometry_count=0
    for width,height,times in product([3,5,7],[2,4,6],[1,2,3]):
        geometry(width,height,times);geometry_count+=1
    cases=[];attempts=0
    # Exhaust all initial memories on the smallest board, and several durations.
    for bits in product([0,1],repeat=6):
        for start in [0,2,4]:
            for steps in [1,2,3,4]:
                attempts+=1;case=one_case(3,2,bits,start,steps)
                if case:cases.append(case)
    rng=random.Random(174)
    for _ in range(72):
        width,height=5,4;bits=[rng.randrange(2) for _ in range(width*height)]
        start=rng.choice([6,8,12]);steps=rng.randrange(1,9)
        attempts+=1;case=one_case(width,height,bits,start,steps)
        if case:cases.append(case)
    # Conditional local tables, including inactive sites, have unique outputs.
    scalar=0
    for color,active,sign in product([0,1],repeat=3):
        if sign>active:continue
        answers=[]
        for new,d,e,f,g,zp in product([0,1],repeat=6):
            if active==d+e and color+e==new+d and d==f+g and sign+g==zp+f:
                answers.append((new,d,e,f,g,zp))
        assert answers==[(color^active,color*active,(1-color)*active,
                          sign*color*active,(1-sign)*color*active,sign^(color*active))]
        scalar+=1
    return dict(geometry_cases=geometry_count,attempted_finite_prefixes=attempts,
                complete_bounded_prefixes=len(cases),conditional_scalar_cases=scalar,
                blank_initial_cases=sum(c['old_word']=='0' for c in cases),samples=cases[:12],
                scope='Exact full outer equations and independent ternary central valuations on bounded genuine histories; no enormous Pell witness tuple, no exhaustive arbitrary-integer soundness test, no periodic input compiler.')


def verify():
    return dict(status='PASS_BOUNDED_ANT_HISTORY_COMPONENT',certificate=certificate(),
                regression=regression(),proof='../1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md',
                scope='Counted existential bounded-board Langton-ant history with complete initial/final board and head parameters. Periodic background construction, raw-input coding, translated patch placement and a universal halting observable are not included.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['certificate']['operations'],result['certificate']['primitive_histogram'])
    print(result['certificate']['groups']);print(result['regression'])
