"""State-top100: reordered program pairs recover the removed zero coordinate."""
from pathlib import Path
import json
import sympy as sp
import explore_doubled_grid_complements as old

PROGRAM=old.PROGRAM
SYM={k:v for k,v in old.SYM.items() if k!='Z'}
OUTER_NAMES=[n for n in old.OUTER_NAMES if n!='Z']
CORE_NAMES=old.CORE_NAMES


def conceptual_fields():
    s=SYM;H=s['H'];t=s['Tgap']
    return [s['Kp'],s['Km'],H-s['Dzero'],s['Dzero'],t-s['A0'],s['A0'],
            t-s['A1'],s['A1'],s['zgrid']*H-s['PV'],s['PV'],PROGRAM['S']*H-s['PC'],s['PC']]


def build():
    # Inline the elementary Z=H-D source elimination over published101.
    # The older un-reordered formal100 exploration is not a dependency.
    prior,old_pairs,old_source,old_origins=old.build()
    keep=[i for i,o in enumerate(old_origins) if o!=21]
    pairs=[old_pairs[i] for i in keep];origins=[old_origins[i] for i in keep]
    sub={old.SYM['Z']:SYM['H']-SYM['Dzero']}
    source=[sp.expand(old_source[i].subs(sub,simultaneous=True)) for i in keep]
    ops=[]
    for name,op,a,b in prior:
        if name=='zero_flag_sum':continue
        if name=='paired_product0':b='PC'
        elif name=='paired_sum0':a='PV'
        elif name=='paired_grid_shift':b=PROGRAM['S']
        elif name=='paired_grid_coefficient':a='zgrid'
        ops.append((name,op,a,b))
    source=list(source)
    raw=sum(f*SYM['q']**i for i,f in enumerate(conceptual_fields()))
    source[origins.index(9)]=sp.expand(2*SYM['r']+1-SYM['q']**12-raw)
    return ops,pairs,source,origins


def verify_certificate():
    ops,pairs,source,origins=build();env=dict(SYM)
    old.old.ALIGNED.baseline.run_schedule(ops,env)
    primitive,counts=old.old.ALIGNED.verify_primitives(ops,env)
    assert len(primitive)==100 and counts=={'+':45,'*':55}
    assert len(source)==len(pairs)==22 and len(OUTER_NAMES+CORE_NAMES)==34
    q=SYM['q'];X=SYM['Km']+q*q*(SYM['Dzero']+q*q*(SYM['A0']+q*q*(SYM['A1']+q*q*(SYM['PV']+q*q*SYM['PC']))))
    raw=sum(f*q**i for i,f in enumerate(conceptual_fields()))
    geometry=source[origins.index(0)];sign=source[origins.index(3)]
    assert sp.expand(env['raw_packed']-raw+geometry*X+sign)==0
    u=2*SYM['r']+1+SYM['j']*SYM['c'];records=[]
    for i,((left,right),poly,origin) in enumerate(zip(pairs,source,origins)):
        correction=0
        if origin==9:correction=geometry*X+sign
        if origin==18:correction=source[origins.index(17)]*(u*u-SYM['y_aux']**2)
        assert sp.expand(env[left]-env[right]-poly-correction)==0,(i,origin)
        records.append(dict(index=i,old_index=origin,equality=[left,right],source=sp.sstr(poly),correction=sp.sstr(correction)))
    return dict(status='PASS',operations=100,primitive_histogram=counts,unknown_count=34,
                positive_unknowns=OUTER_NAMES+CORE_NAMES,equations=22,
                primitive_instructions=primitive,equalities=pairs,residuals=records,
                scope='Exact reordered100 schedule and all22 source comparisons. The omitted Z is reconstructed after controller decoding; the published101 and former OPEN100 sources are untouched.')


def valuation3(n):
    assert n>0
    e=0
    while n%3==0:n//=3;e+=1
    return e,n%3


def verify_program_minimum():
    c=PROGRAM;positions=c['positions'];a=c['a'];d=c['d']
    assert len(a)>=2 and a[0]==min(a)>0 and c['I']==3**a[0]
    assert len(positions)==len(set(positions))
    assert min(positions)==d-max(a) and positions.count(min(positions))==1
    assert c['K']<c['hz'] and c['hs']>=c['g'] and c['hz']>=c['g']
    p=d-max(a)+min(a);assert 0<=p<d
    assert valuation3(c['K']*2*c['I'])==(p,2)
    assert (c['K']*2*c['I'])%(3**(p+1))==2*3**p
    assert all(c['zeros'][v]==0 for v,w in c['edges'] if w==0)
    # The fixed example reaches a true-zero source on every positive return.
    nozero_states={i for i,z in enumerate(c['zeros']) if z==0}
    reached={0};todo=[0];positive_return=False
    while todo:
        v=todo.pop()
        for a0,b in c['edges']:
            if a0!=v:continue
            if b==0:positive_return=True
            if b in nozero_states and b not in reached:reached.add(b);todo.append(b)
    assert not positive_return
    return dict(states=len(a),table_terms=len(positions),minimum_table_exponent=min(positions),
                initial_exponent=min(a),leading_product_exponent=p,marker_exponent=d,
                leading_product_trit=2,table_below_nozero_port=True,
                every_positive_return_has_true_zero=True,
                scope='Exact constants of the maintained example. The proof gives the general table minimum and compiler-prefix arguments; inherited terminal-compiler checks remain separate.')


def verify_carry_lemmas():
    guards=large_guard_carries=top_pairs=top_borrows=odd_successors=prebounds=0
    for R in (27,81,243):
        q=R**3;H=2*(q-1)//(R-1);k=(R-3)//6
        for D in sorted({1,2,H-1,H,H+1,q//3,q-2,q-1}):
            assert 0<D<q;t=k*D
            for A in sorted({1,2,3,q//8,q//4-1}):
                carry,low=divmod(t-A,q);upper=A+carry
                assert -1<=carry<R/6 and 0<=upper<q
                guards+=1;large_guard_carries+=carry>0
    for q in (9,27,81,243):
        for SH in (2,6):
            for incoming in range(0,min(9,q-SH)):
                for C in range(1,q):
                    tc=SH-C+incoming;carry,low=divmod(tc,q);high=C+carry
                    assert carry in (-1,0) and 0<=high<q
                    if old.doubled_word(low) and old.doubled_word(high):
                        top_pairs+=1
                        if tc<0:
                            assert C%2==1 and old.doubled_word(C-1);top_borrows+=1
                        else:assert C%2==0 and C<=SH+incoming
    for width in range(1,11):
        for v in old.words(width):
            assert valuation3(2*v+1)[1]==1;odd_successors+=1
    # These inequalities do not assume powers of three.
    for K in (3,7,11):
        for S in (1,2,5):
            for R in (6*(8*(K+1)*(S+1))+3,3**7):
                assert R-1>8*K*S and R>K and R>=27
                for height in (3,4):
                    q=R**height;H=2*(q-1)//(R-1)
                    assert 4*K*S*H<q and K*K*R<q
                    assert 2*K*(S*H+K)<q
                    assert S*H+K<q
                    # Positive top base excludes C=q+1 before power decoding.
                    assert q**10*((q-1)*(q+1)+S*H)>=q**12
                    prebounds+=1
    return dict(guard_pairs_without_outgoing_carry=guards,positive_internal_guard_carries=large_guard_carries,
                accepted_top_state_windows=top_pairs,negative_top_state_aliases=top_borrows,
                odd_successor_leading_trits=odd_successors,nonpower_inclusive_bound_cases=prebounds,
                scope='Nonvacuous local carry and residue checks. General joint recovery, including the ROM leading-trit exclusion, is proved in the note.')


def canonical(x):
    c=PROGRAM;m=max(c['B'],old.old.EXTRA_EXPONENT+old.old.ELL);m+=(-m)%old.old.ELL;R=3**m
    while (R-1)//(old.old.B0-1)<=old.old.ZON or R<=4*x:m+=old.old.ELL;R*=old.old.B0
    zgrid=(R-1)//(old.old.B0-1)-old.old.ZON
    path=[0,1,2,3,4,5]+[3,1,2,3,4,5]*x+[0]
    blocks=len(path)-1;W=R**3;q=R**blocks;h=(q-1)//(R-1)
    values=[2*x,0,0];a0=a1=kp=km=z0=0
    for b,state in enumerate(path[:-1]):
        lane=b%3;assert c['phases'][state]==lane and (state,path[b+1]) in c['edges']
        n=values[lane];assert 0<=n<R//3
        if c['zeros'][state]:assert n==0
        aa,bb=old.old.ALIGNED.single.split_ternary(n,b);weight=R**b
        a0+=aa*weight;a1+=bb*weight
        if c['signs'][state]>0:kp+=weight
        else:km+=weight
        z0+=c['zeros'][state]*weight;values[lane]+=c['signs'][state];assert min(values)>=0
    assert values==[0,0,0] and c['zeros'][path[-2]]==0 and z0>0
    d=h-z0;t=((R-3)//6)*d
    C=sum(3**c['a'][state]*R**b for b,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*R**b for b,state in enumerate(path[1:]))
    V=c['K']*C-c['g']*Next-c['hs']*kp-c['hz']*d
    original=[kp,km,z0,d,t-a0,a0,t-a1,a1,zgrid*h-V,V,c['S']*h-C,C]
    fields=[2*f for f in original];raw=sum(f*q**i for i,f in enumerate(fields));L=q**12
    assert (L+raw-1)%2==0;r=(L+raw-1)//2
    vals=dict(x=x,q=q,Jrep=q-1,W=W,H=2*h,v=q//W,R=R,Tgap=2*t,A0=2*a0,A1=2*a1,
              Kp=2*kp,Km=2*km,Dzero=2*d,alphaI=R-4*x,PC=2*C,PV=2*V,
              zgrid=zgrid,r=r,beta=L-r)
    assert min(vals.values())>0 and min(fields)>=0
    assert all(f<q and old.old.old.boolean(f//2,m*blocks) for f in fields)
    assert all(f%2==0 for f in fields) and raw%3==2
    assert old.old.old.native(r,12*m*blocks) and r%3==2 and r%2==0 and r<L<r*r
    _,_,source,origins=build();sub={SYM[k]:v for k,v in vals.items()}
    outer=[i for i,o in enumerate(origins) if o<10 or o>=20]
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in outer)
    valuation=old.old.old.central_valuation(r);assert valuation==12*m*blocks
    assert valuation3(2*V)[1]==2
    return dict(x=x,counter_width=m,serial_blocks=blocks,outer_residuals=len(outer),
                doubled_conceptual_fields=12,positive_reconstructed_zero=True,
                packed_bits=r.bit_length(),valuation=valuation,
                scope='Fresh reordered full outer tuple, all12 masks, changed packed index, positive slacks and exact valuation. The general positive converse supplies enormous Pell auxiliaries without numerical instantiation.')


def verify():
    return dict(status='PASS_STATE_TOP_DOUBLED_GRID_100',arithmetic=verify_certificate(),
                program_minimum=verify_program_minimum(),carry_lemmas=verify_carry_lemmas(),
                terminal_compiler=old.verify_terminal_compiler_contract(),canonical=[canonical(1),canonical(2)],
                proof='../1980/EXPLORATION_STATE_TOP_DOUBLED_GRID.md',
                scope='Complete reordered100 construction: author and two independent full proof/source reviews and fresh verification runs passed. The older un-reordered formal100 remains OPEN and the established universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['primitive_histogram'])
    print(result['program_minimum']);print(result['carry_lemmas']);print(result['canonical'])
