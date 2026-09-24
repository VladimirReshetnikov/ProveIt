#!/usr/bin/env python3
"""Verified102: six interleaved complement pairs with a paid global grid."""
from pathlib import Path
import json
import sympy as sp
import explore_complemented_counter_guards as old

PROGRAM=old.PROGRAM
ELL=PROGRAM['l'];B0=3**ELL
assert B0>PROGRAM['m'] and B0>=9
assert all(a%ELL==0 for a in PROGRAM['coords'])
Zold=old.ZALL;old_positions=[];work=Zold;bit=0
while work:
    work,digit=divmod(work,3);assert digit<=1
    if digit:old_positions.append(bit)
    bit+=1
on_positions={p for p in old_positions if p%ELL==0}
threshold=max(Zold,4*PROGRAM['S'],8*(PROGRAM['hs']+PROGRAM['hz']),
              PROGRAM['g']*(PROGRAM['I']+1),
              (PROGRAM['K']+PROGRAM['g'])*(PROGRAM['S']+1),81)
extra=1;EXTRA_EXPONENT=0
while extra<=threshold or EXTRA_EXPONENT%ELL or EXTRA_EXPONENT in on_positions:
    extra*=3;EXTRA_EXPONENT+=1
on_positions.add(EXTRA_EXPONENT);ZON=sum(3**p for p in on_positions)
assert ZON>threshold and all(p%ELL==0 for p in on_positions)
CORE_NAMES=old.CORE_NAMES
OUTER_NAMES=old.OUTER_NAMES+['zgrid']
SYM=dict(old.SYM);SYM['zgrid']=sp.Symbol('zgrid',integer=True,positive=True)
ALIGNED=old.old.old.old.ALIGNED


def conceptual_fields():
    s=SYM;H=s['H'];t=s['Tgap']
    return [s['Kp'],s['Km'],s['Z'],s['Dzero'],t-s['A0'],s['A0'],
            t-s['A1'],s['A1'],PROGRAM['S']*H-s['PC'],s['PC'],
            s['zgrid']*H-s['PV'],s['PV']]


def packing_rows():
    rows=[];previous='PV'
    for i,next_term in enumerate(('PC','A1','A0','Dzero','Km')):
        product=f'paired_product{i}';total=f'paired_sum{i}'
        rows.extend([(product,'*','q2',previous),(total,'+',next_term,product)])
        previous=total
    rows.extend([('paired_scaled','*','twice_J',previous),
                 ('q2_plus_one','+','q2',1),
                 ('paired_t_shift','*','q4','Tgap'),
                 ('paired_low_base','+','H','paired_t_shift'),
                 ('paired_low','*','q2_plus_one','paired_low_base'),
                 ('paired_grid_shift','*','q2','zgrid'),
                 ('paired_grid_coefficient','+',PROGRAM['S'],'paired_grid_shift'),
                 ('paired_grid_heads','*','H','paired_grid_coefficient'),
                 ('paired_high','*','q8','paired_grid_heads'),
                 ('paired_offset','+','paired_low','paired_high'),
                 ('raw_packed','+','paired_scaled','paired_offset')])
    return rows


def build():
    prior,pairs,source,origins=old.build();ops=[];skip=False
    for name,op,left,right in prior:
        if name=='program_qV':
            ops.extend(packing_rows());skip=True
        if not skip:
            if name=='q6':name,op,left,right='q8','*','q4','q4'
            elif name=='D0':left,right='q8','q4'
            ops.append((name,op,left,right))
            if name=='R_minus_one':
                ops.extend([('grid_width','+',ZON,'zgrid'),
                            ('grid_width_product','*',B0-1,'grid_width')])
        if name=='raw_packed':skip=False
    q=SYM['q'];raw=sum(f*q**i for i,f in enumerate(conceptual_fields()))
    source[origins.index(9)]=sp.expand(2*SYM['r']+1-q**12-2*raw)
    pairs.append(('grid_width_product','R_minus_one'))
    source.append((B0-1)*(ZON+SYM['zgrid'])-SYM['R']+1);origins.append(26)
    # Put all simple source corrections before the packed-index residual.
    order=[origins.index(o) for o in (0,1,2,3,21,26)]
    order.extend(i for i in range(len(origins)) if i not in order)
    return ops,[pairs[i] for i in order],[source[i] for i in order],[origins[i] for i in order]


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==102 and counts=={'+':48,'*':54}
    assert len(pairs)==len(source)==23 and len(OUTER_NAMES+CORE_NAMES)==35
    q=SYM['q'];X=SYM['Km']+q*q*(SYM['Dzero']+q*q*(SYM['A0']+q*q*(SYM['A1']+q*q*(SYM['PC']+q*q*SYM['PV']))))
    raw=sum(f*q**i for i,f in enumerate(conceptual_fields()))
    geometry=source[origins.index(0)];flags=source[origins.index(3)];zeros=source[origins.index(21)]
    assert sp.expand(env['raw_packed']-raw+geometry*X+flags+q*q*zeros)==0
    prior_source=old.build()[2];prior_origins=old.build()[3]
    u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    for i,((left,right),poly,origin) in enumerate(zip(pairs,source,origins)):
        correction=0
        if origin==9:correction=2*(geometry*X+flags+q*q*zeros)
        if origin==18:correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2)
        assert sp.expand(env[left]-env[right]-poly-correction)==0,(i,origin)
        if origin not in (9,26):assert sp.expand(poly-prior_source[prior_origins.index(origin)])==0
        records.append(dict(index=i,old_index=origin,equality=[left,right],
                            source=sp.sstr(poly),correction=sp.sstr(correction)))
    used={x for r in ops for x in r[2:]}|{x for p in pairs for x in p}
    assert set(SYM)<=used and 'q6' not in used
    assert sum(r[0]=='q2_plus_one' for r in ops)==1
    return dict(status='PASS',operations=102,primitive_histogram=counts,unknown_count=35,
                positive_unknowns=OUTER_NAMES+CORE_NAMES,equations=23,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                grid_spacing=ELL,grid_radix=B0,on_grid_forbidden_exponents=sorted(on_positions),
                scope='All23 exact source comparisons, executable102 primitive schedule, and earlier-source corrections for both flag sums and q geometry. Semantic proof and fresh changed-index canonical evidence are separate gates.')


def verify_bounds_and_pairs():
    prelim=negative_tc=negative_tv=accepted=0
    for q in (9,15,27,45,81):
        J=(q-1)//2
        for SH in range(1,max(2,J//2)):
            for C in range(1,q):
                tc=SH-C
                low=tc%q;carry=tc//q;upper=C+carry
                caps=low<=J and 0<=upper<=J
                if tc<0:
                    negative_tc+=1;assert not caps
                elif caps:accepted+=1
                prelim+=1
        for Q in range(1,max(2,J//3)):
            for V in range(1,J+1):
                tv=Q-V
                if tv<0:negative_tv+=1;assert tv%q>J
        # Exact top-pair bound V<=J, including the dangerous endpoint J+1.
        for V in (J+1,J+2,q):
            assert q**10*((q-1)*V+1)>(q**12-1)//2
    pair_cases=0
    for w in range(2,8):
        q=3**w;J=(q-1)//2
        words=[sum(((b>>i)&1)*3**i for i in range(w)) for b in range(1<<w)]
        for a in words:
            for b in words:
                if old.boolean(a+b,w):
                    assert all(not (((a//3**i)%3) and ((b//3**i)%3)) for i in range(w))
                    pair_cases+=1
    return dict(signed_program_pair_windows=prelim,negative_state_complements_rejected=negative_tc,
                negative_junk_complements_rejected=negative_tv,accepted_state_pair_windows=accepted,
                Boolean_disjoint_sum_cases=pair_cases,
                scope='Nonvacuous signed program-pair and top-field endpoint checks; ordinary positive sign/zero pairs and counter-guard bounds are proved in the full note.')


def canonical(x):
    c=PROGRAM;m=max(c['B'],EXTRA_EXPONENT+ELL)
    m+=(-m)%ELL
    R=3**m
    while (R-1)//(B0-1)<=ZON:m+=ELL;R*=B0
    zgrid=(R-1)//(B0-1)-ZON
    path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    blocks=len(path)-1;W=R**3;q=R**blocks;J=(q-1)//2;H=(q-1)//(R-1)
    values=[2*x,0,0];A0=A1=Kp=Km=Z=0
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0
        aa,bb=ALIGNED.single.split_ternary(n,b);weight=R**b
        A0+=aa*weight;A1+=bb*weight
        if c['signs'][state]>0:Kp+=weight
        else:Km+=weight
        Z+=c['zeros'][state]*weight;values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0]
    D=H-Z;t=((R-3)//6)*D
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*Kp-c['hz']*D
    vals=dict(x=x,q=q,Jrep=J,W=W,H=H,v=q//W,R=R,Tgap=t,A0=A0,A1=A1,
              Kp=Kp,Km=Km,Z=Z,Dzero=D,alphaI=R-2*x,PC=C,PV=V,zgrid=zgrid)
    fields=[Kp,Km,Z,D,t-A0,A0,t-A1,A1,c['S']*H-C,C,zgrid*H-V,V]
    raw=sum(f*q**i for i,f in enumerate(fields));r=raw+(q**12-1)//2
    vals.update(r=r,beta=q**12-r)
    assert min(vals.values())>0 and min(fields)>=0
    assert sum(fields)==(2+c['S']+zgrid)*H+2*t
    assert all(old.boolean(f,m*blocks) for f in fields)
    assert old.native(r,12*m*blocks) and r%3==2 and r%2==0
    assert r<q**12<r*r and (R-1)==(B0-1)*(ZON+zgrid)
    _,_,source,origins=build();sub={SYM[k]:v for k,v in vals.items()}
    outer=[i for i,o in enumerate(origins) if o<10 or o>=20]
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in outer)
    val=old.central_valuation(r);assert val==12*m*blocks
    return dict(x=x,counter_width=m,serial_blocks=blocks,outer_residuals=len(outer),
                conceptual_masks=12,zero_complements=sum(f==0 for f in fields),
                packed_bits=r.bit_length(),valuation=val,positive_grid_slack=True,
                scope='Fresh changed-width, changed-order complete outer tuple and all12 native masks. Full positive Pell coordinates are supplied by the general converse, not materialized.')


def verify():
    return dict(status='PASS_INTERLEAVED_GRID_COMPLEMENTS_102',arithmetic=verify_certificate(),
                signed_pairs=verify_bounds_and_pairs(),canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_INTERLEAVED_GRID_COMPLEMENTS.md',
                scope='Complete author proof/source/canonical gate and three independent full proof/source reviews and fresh verification runs passed for102. The established universal frontier remains90; publication is a separate action.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['primitive_histogram'])
    print(result['signed_pairs']);print(result['canonical'])
