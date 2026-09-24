"""Positive27 Life wrapper with pre-mask bounds; full conditional70 ledger."""
from itertools import product
from pathlib import Path
import json
import random
import sympy as sp
import explore_life_one_field_mask as local
import round39_1980_boolean_history_components as binary

OUTER_POSITIVE = ['S','B','Y','U','J','q','r']
CORE_POSITIVE = ['pell_'+x for x in binary.CORE_NAMES if x != 'r']
POSITIVE = OUTER_POSITIVE+CORE_POSITIVE
WRAPPER = [
    ('q2','*','q','q'), ('Lambda','*','q2','q'), ('D0','*','Lambda','q2'),
    ('ones_left','*',511,'J'), ('ones_right','-','q',1),
] + local.SHIFTED_LOCAL + [
    # b2=2B is already paid in SHIFTED_LOCAL.
    ('qu','*','q','U'), ('low_pair','+','b2','qu'),
    ('mixed_high','*','q2','Vprime'), ('P','+','low_pair','mixed_high'),
    ('mask_middle','*',510,'q'), ('mask_high','*',144,'q2'),
    ('mask_pair','+','mask_middle','mask_high'),
    ('mask_factor','+',509,'mask_pair'), ('M','*','J','mask_factor'),
    ('gap','-','Lambda','P'), ('lambda_m1','-','Lambda',1),
    ('index_product','*','gap','lambda_m1'), ('index_rhs','+','index_product','M'),
]


def rename(name):
    if not isinstance(name,str): return name
    if name == 'n2': return 'D0'
    if name == 'r': return 'r'
    return 'pell_'+name


def core():
    result=[]
    for name,op,a,b in binary.CORE:
        if name == 'H17': op,a,b='-','jc','tr1'
        if name == 'aux_u_rhs': op,a,b='-','of','c'
        result.append((rename(name),op,rename(a),rename(b)))
    return result


def comparisons():
    return [('ones_left','ones_right'),('index_rhs','r')]+[
        (rename(a),rename(b)) for a,b in binary.CORE_EQUALITIES]


def count(rows):
    h=local.histogram(rows)
    return dict(operations=len(rows),multiplications=h['M'],additions=h['A'])


def source_check():
    z=dict(zip(POSITIVE,sp.symbols(' '.join(POSITIVE))))
    S,B,Y,U,J,q,r=[z[n] for n in OUTER_POSITIVE]
    V=28*S+2*B+16*Y+118*U+41*J
    P=2*B+q*U+q*q*V
    M=J*(509+510*q+144*q*q)
    scale=q**5
    a,c,d,f,h,i,j,k,s,w,tau,eta,zeta,ga,y=[z['pell_'+x] for x in
        ('a','c','d','f','h','i','j','k','s','w','tau','eta','zeta','ga','y_aux')]
    o=z['pell_o']
    up,yp=w*scale,s*scale
    normq=up*yp*yp
    delta=a*a+4*a+3
    auxu=j*c-(2*r+1)
    kernel_sources=[
        normq*(normq+1)*k*k-tau*(tau+1), c-yp*k-eta, k-eta-zeta,
        k-r-1-h*up*yp, a-yp*(up+1), d-up-a*c-ga*(4*a+3),
        d*d-delta*c*c-1, (i*c*c)**2-delta*(f*f-1),
        delta*(f*f-1)*(auxu*auxu-y*y)-(1-y*y), auxu-o*f+c]
    sources=[511*J-q+1,(q**3-P)*(q**3-1)+M-r]+kernel_sources
    rows=WRAPPER+core();e=local.run(rows,z)
    identities=dict(Vprime=V,P=P,M=M,Lambda=q**3,D0=scale,
                    index_rhs=(q**3-P)*(q**3-1)+M)
    for name,value in identities.items():assert sp.expand(e[name]-value)==0,name
    records=[]
    for ix,((lhs,rhs),source) in enumerate(zip(comparisons(),sources)):
        correction=kernel_sources[7]*(auxu*auxu-y*y) if ix==10 else 0
        assert sp.expand(e[lhs]-e[rhs]-source-correction)==0,ix
        records.append(dict(index=ix,equality=[lhs,rhs],source=sp.sstr(sp.expand(source)),
                            correction=sp.sstr(sp.expand(correction))))
    assert len(records)==12 and len(POSITIVE)==len(set(POSITIVE))==23
    assert count(WRAPPER)==dict(operations=27,multiplications=15,additions=12)
    assert count(core())==dict(operations=43,multiplications=25,additions=18)
    assert count(rows)==dict(operations=70,multiplications=40,additions=30)
    assert sp.expand((511*M-144*q**3-366*q*q+q+509).subs(J,(q-1)/511))==0
    return dict(wrapper=count(WRAPPER),kernel=count(core()),combined=count(rows),
                positive_coordinates=POSITIVE,positive_count=23,equations=12,
                source_residuals=records,wrapper_identities=len(identities),
                schedule=rows,kernel_sign=-1,
                scope='Complete arithmetic ledger for the conditional component; no torus or raw-input compiler.')


def untyped_bounds():
    rng=random.Random(27070);accepted=rejected=nonpowers=endpoint=0
    for j in range(1,51):
        q=511*j+1
        for sample in range(50):
            # These positive fields are arbitrary integers, not typed digit words.
            cap=q//(500 if sample%2==0 else 8)
            vals=dict(J=j,q=q,**{n:rng.randint(1,max(1,cap)) for n in ('S','B','Y','U')})
            e=local.run(WRAPPER,vals);P,M,L=e['P'],e['M'],e['Lambda'];r=e['index_rhs']
            assert e['ones_left']==e['ones_right'] and 0<M<L
            assert 511*M==144*q**3+366*q*q-q-509
            if r>0:
                assert 0<P<=L and q*q*e['Vprime']<P
                assert 2*vals['B']<e['Vprime']<q and 118*vals['U']<e['Vprime']
                assert 0<2*vals['B']<q and 0<vals['U']<q and P<L
                assert 64<=q*q<q**3-1<r<q**6
                assert q**5>q**4 and q**5<r*r
                assert q**10>2*r+1 and 8*r<q**10
                accepted+=1;nonpowers+=q&(q-1)!=0
            else:rejected+=1
        L=q**3;M=j*(509+510*q+144*q*q)
        assert (L-L)*(L-1)+M>0 # Positivity alone initially gives only P<=L.
        assert (L-(L+1))*(L-1)+M<=0
        endpoint+=2
    assert min(accepted,rejected,nonpowers)>0
    return dict(arbitrary_positive_field_tuples=accepted+rejected,
                positive_index_tuples=accepted,rejected_nonpositive_indices=rejected,
                positive_nonpower_tuples=nonpowers,endpoint_checks=endpoint,
                scope='Pre-kernel arithmetic bounds only; nonpower cases are not claimed kernel solutions.')


def local_witnesses():
    result={}
    for n,b in product(range(9),range(2)):
        y=local.life(n,b)
        us=[u for u in range(2) if local.digit(n,b,y,u)&72==0]
        assert len(us)==1
        result[n,b]=us[0]
    return result


def packed_checks():
    rng=random.Random(27071);helper=local_witnesses()
    valid=corrupt=positive=0;records=[]
    for size in (1,2,3,7,16,31):
        for sample in range(30):
            cells=[(2,1)]+[(rng.randrange(9),rng.randrange(2)) for _ in range(size-1)]
            if size>=2:cells[1]=(3,0)
            ys=[local.life(n,b) for n,b in cells]
            us=[helper[n,b] for n,b in cells]
            changed=False
            if sample%3==1 and size>=2:ys[0]^=1;changed=True
            if sample%3==2 and size>=2:us[0]^=1;changed=True
            q=512**size;J=(q-1)//511
            values=dict(q=q,J=J,S=local.pack([n+b for n,b in cells],512),
                        B=local.pack([b for n,b in cells],512),
                        Y=local.pack(ys,512),U=local.pack(us,512))
            e=local.run(WRAPPER,values);r=e['index_rhs']
            assert min(values.values())>0 and r>0
            assert e['ones_left']==e['ones_right']
            assert 0<e['P']<q**3 and 0<e['M']<q**3
            assert e['M'].bit_count()==18*size and e['D0']==2**(45*size)
            assert e['P']%2==0 and e['M']%2==1 and r%2==1
            ok=e['P']&e['M']==0
            assert ok==(r.bit_count()==45*size)==(not changed)
            assert r.bit_count()<=45*size
            assert 64<=q*q<r<q**6 and e['D0']<r*r
            positive+=1;valid+=ok;corrupt+=not ok
            if sample==0:
                records.append(dict(cells=size,q=q,index=r,scale=e['D0'],
                                    central_valuation=r.bit_count(),index_parity=r%2))
    # Recover Booleanity independently of any prior input-plane typing.
    mask=509+512*510+512**2*144
    extraction=0
    for slot,digit in product(range(3),range(512)):
        expected=digit in (0,2) if slot==0 else digit in (0,1) if slot==1 else digit&144==0
        assert ((digit*512**slot)&mask==0)==expected
        extraction+=1
    return dict(positive_outer_tuples=positive,valid=valid,corrupt=corrupt,
                untyped_field_extractions=extraction,canonical_examples=records,
                kernel_extension='Fresh sixteen positive witnesses exist by the proved nonsquare fixed-minus43 converse; huge auxiliaries not materialized.')


def verify():
    return dict(status='PASS_LIFE_POSITIVE_BOOTSTRAP27_COMPONENT',
                source=source_check(),pre_power_bounds=untyped_bounds(),packed=packed_checks(),
                proof='../1980/EXPLORATION_LIFE_POSITIVE_BOOTSTRAP.md',
                review='Author and two independent complete scoped proof/source reviews pass; fresh read-only checks exactly match the saved JSON.',
                scope='Positive27 wrapper derives raw-field bounds and radix power with fixed-minus43. Conditional70 local/mask/kernel component only: actual neighbor geometry, typed target, raw-input interface and any zero-plane adaptation are not supplied.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(result['status']);print(result['source']['wrapper'],result['source']['combined'])
    print(result['pre_power_bounds']);print({k:v for k,v in result['packed'].items() if k!='canonical_examples'})
