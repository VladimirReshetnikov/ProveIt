"""Actual empty-graph constants for a full merged-word source counterfamily.

The repetition count is constructive but is not numerically materialized.
"""
from pathlib import Path
import json
from math import gcd
import explore_rom_zero_mask_omission as empty

def digits(n):
    out=set();i=0
    while n:
        n,t=divmod(n,3);assert t<2
        if t:out.add(i)
        i+=1
    return out

def fixed_constants():
    old=empty.program();ell=old['ell'];a=old['a']
    assert 3**ell>len(a)
    shift=max(a)+ell-min(old['positions']);shift+=(-shift)%ell
    scale=3**shift;K=old['K']*scale;g=old['g']*scale
    hs=old['hs']*scale;hz=old['hz']*scale;I=3**a[0]
    copy=min(old['positions'])+shift;assert copy>max(a)
    union=set();row_cases=[]
    for i,j in old['edges']:
        f=(K+1)*3**a[i]-g*3**a[j]-hs*int(old['signs'][i]>0)-hz*(1-old['zeros'][i])
        support=digits(f);assert f>3**a[i]
        assert f%3**copy==3**a[i] and all(p%ell==0 for p in support)
        union|=support;row_cases.append((i,j,len(support)))
    U=sum(3**p for p in union);c=I;assert c>0 and a[0] in union and U>c
    positivity=(K-1)*(U-c)-(hs+hz+g*I)
    assert positivity>0
    threshold=max(2*U,(K+g)*(old['S']+1),g*(I+1),hs+hz,81)
    exponent=0;Zon=1
    while Zon<=threshold or exponent%ell:Zon*=3;exponent+=1
    m=exponent+ell;R=3**m;B0=3**ell
    while (R-1)//(B0-1)<=Zon:m+=ell;R*=B0
    zgrid=(R-1)//(B0-1)-Zon
    assert zgrid>0 and R>2*U and R%g==0
    T=R//g;den=(K+1)*T-1
    assert den>1 and gcd(R,den)==gcd(T*c*R**12,den)==1
    # The fixed sufficient bound implies the full width-dependent one.
    assert (T*K-1)*(U-c)>T*(hs+hz)+I*(R-1)
    return dict(old=old,K=K,g=g,hs=hs,hz=hz,I=I,U=U,c=c,
        R=R,m=m,Zon=Zon,zgrid=zgrid,T=T,den=den,
        report=dict(states=len(a),edges=len(old['edges']),grid_spacing=ell,
            added_g_exponent=shift,copy_boundary=copy,fixed_union_positions=len(union),
            fixed_width_exponent=m,paid_threshold_exponent=exponent,
            all_correct_merged_rows_checked=len(row_cases),
            fixed_positivity_margin_bits=positivity.bit_length(),
            modulus_bits=den.bit_length(),positive_width_slack=True,
            modulation_coefficient_coprime=True))

def split(n):
    a=b=0;p=1
    while n:
        n,t=divmod(n,3)
        if t:a+=p
        if t==2:b+=p
        p*=3
    return a,b

def numeric_history(c,loops):
    R=c['R'];W=R**3;signs=[1,1,1,-1,-1,-1,-1,1,1,-1,-1,-1]+[1,1,1,-1,-1,-1]*loops
    values=[2,0,0];A0=A1=kp=km=0;z=R;source_count=0
    for row,sign in enumerate(signs):
        n=values[row%3];assert 0<=n<R//3
        if row==1:assert n==0
        a,b=split(n);assert a+b==n
        A0+=a*R**row;A1+=b*R**row
        if sign>0:kp+=R**row
        else:km+=R**row
        values[row%3]+=sign;assert min(values)>=0;source_count+=1
    assert values==[0,0,0]
    u=len(signs);q=R**u;H=(q-1)//(R-1);D=H-z;t=(R-3)//6*D
    assert min(A0,A1,kp,km,z,D,t)>0 and kp+km==z+D==H
    assert W*(A0+A1+kp-km)==A0+A1-2
    assert min(t-A0,t-A1)>=0
    for v in (kp,km,z,D,t-A0,A0,t-A1,A1):digits(v)
    assert H%2==0 and u%6==0
    return dict(loops=loops,serial_rows=u,checked_numeric_sources=source_count,
        exact_time_equation=True,all_eight_counter_fields_Boolean=True,
        all_supplied_counter_words_positive=True,even_head_repunit=True)

def empty_graph_contract(c):
    old=c['old'];values=[2,0,0]
    assert old['edges']==[(i,i+1) for i in range(17)]+[(17,12),(17,0)]
    for state in range(6):
        lane=state%3
        if old['zeros'][state]:assert values[lane]==0
        values[lane]+=old['signs'][state]
    assert values==[2,0,0] and old['zeros'][6]==1
    return dict(compulsory_false_state=6,false_source_at_x1=2,
        first_return_passes_state6=True,
        scope='The same six-step prefix restores[2x,0,0] for every x>0; mandatory state6 requests its positive first register to be zero. Thus the fixed graph accepts no positive input.')

def verify():
    c=fixed_constants()
    return dict(status='PASS_ACTUAL_EMPTY_GRAPH_MERGED_WORD_COUNTERFAMILY',
        constants=c['report'],empty_graph=empty_graph_contract(c),
        numeric_histories=[numeric_history(c,n) for n in (0,1,2)],
        construction=dict(input=1,prefix_rows=12,loop_period=6,
            loops='d*ord_d(R^6)',base_word='(U-c)*H',
            toggles='At most d-1 selected loop-start copies of c; route residues differ by one invertible common weight.',
            mask_fields=10,Pell_scale='q^10',even_index=True),
        proof='../1980/EXPLORATION_MERGED_PROGRAM_EMPTY_GRAPH.md',
        scope='Actual fixed empty-controller constants and positive uniform bound, real finite raw-counter templates, and a constructive unmaterialized modular-fill/full-Pell extension. The enormous repetition and Pell coordinates are not numerically instantiated; the general proof supplies them.')

if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status']);print(result['constants']);print(result['numeric_histories'])
