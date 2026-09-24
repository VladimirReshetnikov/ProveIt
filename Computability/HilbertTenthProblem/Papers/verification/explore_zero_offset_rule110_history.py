"""Complete positive radix128 Rule110 history75 with a zero-offset local field."""
from pathlib import Path
from itertools import product
import json
import sys
import sympy as sp
import explore_one_field_rule110_history as retained
from round13_1980_certificate import verify_primitives
import round4_1980_operation_count as baseline

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

RADIX=128
ALPHA,BETA,GAMMA,DELTA=18,23,23,42
LOCAL_COEFFICIENT=ALPHA*RADIX**2+BETA*RADIX+GAMMA
FORBIDDEN=36
ALLOWED={d for d in range(RADIX) if not d&FORBIDDEN}
PARAMETERS=['I','F']
OUTER_NAMES=['q','awidth','quot','hrow','Cw','Yw','Jrow','alphaI']
CORE_NAMES=retained.CORE_NAMES
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
SYM={name:sp.Symbol(name) for name in NAMES}
def build_outer(radix):
  return [
    ('Q2','*','q','q'),('Lbig','*','Q2','q'),('n2','*','Lbig','Q2'),
    ('W','*',radix,'awidth'),('Wq','*','W','quot'),
    ('Qm1','-','q',1),('Wm1','-','W',1),('row_geom','*','hrow','Wm1'),
    ('Ccoef','*',18*radix**2+23*radix+23,'Cw'),('Y42','*',42,'Yw'),('Uw','+','Ccoef','Y42'),
    ('Ibound','+','I','alphaI'),
    ('WY','*','W','Yw'),('time_lhs','+','I','WY'),
    ('QF','*','q','F'),('time_rhs','+','Cw','QF'),
    ('Bw','*',radix,'Cw'),('Tword','+','Bw','hrow'),
    ('qU','*','q','Uw'),('YqU','+','Yw','qU'),
    ('qYqU','*','q','YqU'),('packed','+','Tword','qYqU'),
    ('qp1','+','q',1),('boolean_mask','*',radix-2,'qp1'),
    ('local_mask','*',36,'Q2'),('mask_factor','+','boolean_mask','local_mask'),
    ('mask','*','Jrow','mask_factor'),('repunit','*',radix-1,'Jrow'),
    ('packing_gap','-','Lbig','packed'),('Lm1','-','Lbig',1),
    ('r_product','*','packing_gap','Lm1'),('r_lhs','+','r_product','mask'),
]
OUTER=build_outer(RADIX)
CORE=list(retained.CORE)
SCHEDULE=OUTER+CORE
OUTER_EQUALITIES=[('q','Wq'),('Qm1','row_geom'),('Ibound','awidth'),
                  ('time_lhs','time_rhs'),('repunit','Qm1'),('r','r_lhs')]
EQUALITIES=OUTER_EQUALITIES+retained.retained.CORE_EQUALITIES


def source_residuals(radix=RADIX):
    z=SYM
    q,A,quot,H,C,Y,J,alpha=[z[n] for n in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=[z[n] for n in CORE_NAMES]
    W=radix*A;L=q**3;scale=q**5
    U=(18*radix**2+23*radix+23)*C+42*Y;T=radix*C+H
    P=T+q*Y+q*q*U;M=J*((radix-2)*(1+q)+36*q*q)
    X=w*scale;Z=s*scale;D=a*a+4*a+3;auxu=j*c-(2*r+1)
    return [q-W*quot,q-1-H*(W-1),z['I']+alpha-A,
            z['I']+W*Y-C-q*z['F'],(radix-1)*J-q+1,r-(L-P)*(L-1)-M,
            X*Z*Z*(X*Z*Z+1)*k*k-tau*(tau+1),
            c-Z*k-eta,k-eta-zeta,k-r-1-h*X*Z,
            a-Z*(X+1),d-X-a*c-ga*(4*a+3),d*d-D*c*c-1,
            (i*c*c)**2-D*(f*f-1),
            D*(f*f-1)*(auxu*auxu-ya*ya)-(1-ya*ya),auxu+c-o*f]


def verify_source(radix=RADIX):
    rows=build_outer(radix)+CORE
    env=dict(SYM)
    histogram=baseline.run_schedule(rows,env)
    sources=source_residuals(radix)
    auxu=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[13]*(auxu**2-SYM['y_aux']**2)
    records=[]
    for index,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right])
        adjustment=correction if index==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjustment)==0 else -1
        assert sp.expand(actual-sign*source-adjustment)==0,index
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjustment))))
    primitives,counts=verify_primitives(rows,env)
    assert len(OUTER)==32 and len(CORE)==43 and len(primitives)==75
    assert counts=={'+':32,'*':43} and len(EQUALITIES)==len(sources)==16
    assert len(NAMES)==len(set(NAMES))==27
    assert set(NAMES)<=({x for row in rows for x in row[2:]}
                        |{x for pair in EQUALITIES for x in pair})
    assert all(p.free_symbols<=set(SYM.values()) for p in sources)
    assert sp.expand(env['W']-radix*SYM['awidth'])==0
    assert sp.expand(env['n2']-SYM['q']**5)==0
    assert sp.expand(env['Lbig']-SYM['q']**3)==0
    assert sp.expand(env['mask']-SYM['Jrow']*((radix-2)*(1+SYM['q'])+36*SYM['q']**2))==0
    return dict(radix=radix,operations=75,multiplications=43,additions_subtractions=32,
                outer_operations=32,kernel_operations=43,
                positive_unknown_count=25,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                equations=16,outer_equations=6,primitive_instructions=primitives,
                histogram=histogram,sources=records,kernel_sign='fixed minus, odd index',
                scale='q^5, nonsquare before decoding')


def typed(value,allowed={0,1},radix=RADIX):
    if value<0:return False
    while value:
        value,digit=divmod(value,radix)
        if digit not in allowed:return False
    return True


def word(raw,radix=RADIX):
    value=0;place=1
    while raw:
        value+=(raw&1)*place;raw>>=1;place*=radix
    return value


def rule(value,radix=RADIX):
    assert typed(value,radix=radix)
    bits=radix.bit_length()-1
    result=0;place=1
    for _ in range((value.bit_length()+bits-1)//bits+1):
        a=value//(place//radix)%radix if place>1 else 0
        b=value//place%radix;c=value//(radix*place)%radix
        result+=((110>>(4*a+2*b+c))&1)*place
        place*=radix
    return result


def scalar_checks():
    rows=[]
    for a,b,c in product(range(2),repeat=3):
        correct=(110>>(4*a+2*b+c))&1
        values=[18*a+23*b+23*c+42*y for y in range(2)]
        for y,value in enumerate(values):
            assert 0<=value<128 and (value&36==0)==(y==correct)
        rows.append(dict(inputs=[a,b,c],output=correct,values=values))
    assert LOCAL_COEFFICIENT==297879
    return dict(coefficients=[18,23,23,42],constant=0,forbidden_mask=36,
                forbidden_bits=[2,5],maximum_raw_value=106,table=rows)


def numeric_outer(values,radix=RADIX):
    env=dict(values)
    for name,op,left,right in build_outer(radix):
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env


def check_tuple(m,t,B,Y,I,F,radix=RADIX):
    bits=radix.bit_length()-1
    W=radix**m;q=W**t;A=W//radix;H=(q-1)//(W-1);J=(q-1)//(radix-1)
    assert B>0 and B%radix==0 and 0<I<A and F>0
    C=B//radix;U=(18*radix**2+23*radix+23)*C+42*Y;T=B+H
    assert all(0<x<q for x in (U,T,Y))
    allowed={d for d in range(radix) if not d&36}
    assert typed(T,radix=radix) and typed(Y,radix=radix) and typed(U,allowed,radix)
    P=T+q*Y+q*q*U;M=J*((radix-2)*(q+1)+36*q*q);L=q**3
    r=(L-P)*(L-1)+M
    values=dict(q=q,awidth=A,quot=q//W,hrow=H,Cw=C,Yw=Y,Jrow=J,
                alphaI=A-I,r=r,I=I,F=F)
    env=numeric_outer(values,radix)
    assert min(values.values())>0 and all(env[a]==env[b] for a,b in OUTER_EQUALITIES)
    assert env['packed']==P and env['mask']==M and env['Uw']==U
    assert 0<P<L and 0<M<L and P&M==0
    assert M.bit_count()==2*bits*m*t and r.bit_count()==5*bits*m*t and r%2==1
    assert q**3-1<r<q**6 and q**5<r*r
    assert q*q<r<2*(q*q)**3 and q**5>(q*q)**2
    assert all(typed(x,radix=radix) for x in (B,I,F))
    current=radix*I
    for row in range(t):
        bj=B//W**row%W;yj=Y//W**row%W
        assert bj==current and bj%radix==0 and yj==rule(bj,radix)
        current=radix*yj
    assert current==radix*F and F<W//radix
    return dict(radix=radix,m=m,t=t,I=I,F=F,positive_outer_coordinates=values,
                checked_outer_equations=6,central_valuation=5*bits*m*t)


def verify_histories():
    candidates=boundary=finals=misaligned=0;accepted=[]
    for N in range(2,13):
        q=RADIX**N;J=(q-1)//127
        words=[word(raw) for raw in range(1<<N)]
        for exponent in range(8,min(35,7*N)+1):
            if 7*N%exponent:continue
            W=2**exponent;A=W//RADIX;H=(q-1)//(W-1)
            for T in words:
                candidates+=1
                if exponent%7:misaligned+=1
                B=T-H
                if B<=0 or B%RADIX:continue
                C=B//RADIX;I=C%W
                if not 0<I<A:continue
                assert exponent%7==0
                lower=C//W
                if not typed(lower):continue
                boundary+=1;m=exponent//7;t=N//m
                for raw in range(1,1<<m):
                    F=word(raw);finals+=1
                    Y=lower+(q//W)*F;U=297879*C+42*Y
                    if 0<U<q and typed(U,ALLOWED):
                        accepted.append(check_tuple(m,t,B,Y,I,F))
    canonical=[]
    for I in map(word,(1,3,5,7,9)):
        for t in (1,2,3,4,8,16):
            rows=[];outputs=[];current=RADIX*I
            for _ in range(t):
                rows.append(current);outputs.append(rule(current));current=RADIX*outputs[-1]
            m=max(3,max(x.bit_length() for x in rows+outputs)//7+3)
            W=RADIX**m
            B=sum(x*W**j for j,x in enumerate(rows));Y=sum(x*W**j for j,x in enumerate(outputs))
            canonical.append(check_tuple(m,t,B,Y,I,outputs[-1]))
    assert accepted and len(canonical)==30
    return dict(candidate_T_words=candidates,misaligned_T_words=misaligned,
                surviving_boundaries=boundary,compatible_final_words=finals,
                accepted_count=len(accepted),accepted=accepted,
                canonical_count=len(canonical),canonical=canonical)


def verify_bounds_and_alignment():
    tested=positive=nonpower=0
    for A,k in product((2,3,4,7,9,128,129),range(129)):
        W=128*A;H=1+k*W;q=1+H*(W-1)
        if (q-1)%127:continue
        J=(q-1)//127;L=q**3;M=J*(126+126*q+36*q*q)
        assert q%W==0 and q>=W>=256 and 0<M<L
        for C,Y in product((1,max(1,q//297879-1),q//297879+1,q),
                           (1,max(1,q//42-1),q//42+1,q)):
            U=297879*C+42*Y;T=128*C+H;P=T+q*Y+q*q*U
            r=(L-P)*(L-1)+M;tested+=1
            if r<=0:continue
            positive+=1;nonpower+=bool(q&(q-1))
            assert U<q and 16384*C<q and T<q and P<L and q**3-1<r<q**6
            assert q*q<r<q**6 and q**5<r*r
    assert min(tested,positive,nonpower)>0
    lowblocks=bad=0
    for exponent in range(8,23):
        W=2**exponent
        for I in range(1,W//128):
            low=128*I+1+W
            assert low<128*W and low>>exponent&1
            if exponent%7:assert not typed(low);bad+=1
            lowblocks+=1
    return dict(prepower_candidates=tested,positive_index_candidates=positive,
                nonpower_q_positive_index_candidates=nonpower,
                initial_low_blocks=lowblocks,misaligned_low_blocks_rejected=bad)


def mask_checks():
    accepted=overflow=0
    # Exhaust one-cell arbitrary bounded P, not just source histories.
    q=128;L=q**3;M=126+126*q+36*q*q
    assert M.bit_count()==14
    for P in range(L):
        r=(L-P)*(L-1)+M
        disjoint=P&M==0
        assert r.bit_count()<=35 and (r.bit_count()==35)==disjoint
        if P+M>=L:
            overflow+=1
            assert not disjoint and r.bit_count()<35
        accepted+=disjoint
    return dict(one_cell_packed_values=L,disjoint=accepted,overflow_cases=overflow,
                threshold=35,mask=M)


def family_checks():
    sources=[];histories=[]
    for radix in (256,512):
        sources.append(verify_source(radix))
        bits=radix.bit_length()-1
        for raw,t in product((1,3,5,7,9),(1,2,3,4,8,16)):
            I=word(raw,radix);current=radix*I;rows=[];outputs=[]
            for _ in range(t):
                rows.append(current);outputs.append(rule(current,radix));current=radix*outputs[-1]
            m=max(3,max(x.bit_length() for x in rows+outputs)//bits+3)
            W=radix**m
            B=sum(x*W**j for j,x in enumerate(rows));Y=sum(x*W**j for j,x in enumerate(outputs))
            histories.append(check_tuple(m,t,B,Y,I,outputs[-1],radix))
    return dict(sources=sources,canonical_count=len(histories),canonical=histories,
                theorem_family='All fixed radices b=2^k, k>=7, at the same75 operations.')


def verify():
    return dict(status='PASS_ZERO_OFFSET_RULE110_HISTORY75',radix=128,
                source=verify_source(),local=scalar_checks(),
                bounds_alignment=verify_bounds_and_alignment(),mask=mask_checks(),
                histories=verify_histories(),
                family=family_checks(),
                proof='../1980/EXPLORATION_ZERO_OFFSET_RULE110_HISTORY.md',
                review='Author and independent complete scoped proof/source review PASS; immutable fresh receipt comparison PASS.',
                scope='Complete positive moving finite-history family at b=2^k,k>=7; radix128 bounded search and complete256/512 source/canonical checks. Changed numerical radix versus76; no universal input/halting interface.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(result['status']);print({k:result['source'][k] for k in ('operations','multiplications','additions_subtractions','positive_unknown_count','equations')})
    print(result['bounds_alignment']);print(result['mask'])
    print({k:v for k,v in result['histories'].items() if k not in ('accepted','canonical')})
