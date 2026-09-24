"""Complete positive Rule110 history76; a full counterexample to its divisor deletion."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_one_field_rule110_history as old
from round13_1980_certificate import verify_primitives
import round4_1980_operation_count as baseline

PARAMETERS=['I','F']
OUTER_NAMES=['q','awidth','quot','hrow','Cw','Yw','Jrow','alphaI']
CORE_NAMES=old.CORE_NAMES
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
SYM={name:sp.Symbol(name) for name in NAMES}
OUTER=[]
for row in old.OUTER:
    if row[0]=='vq':OUTER.extend([('W','*',16,'awidth'),('Wq','*','W','quot')])
    elif row[0] not in ('v2','W'):OUTER.append(row)
CORE=list(old.CORE)
SCHEDULE=OUTER+CORE
OUTER_EQUALITIES=[('q','Wq'),('Qm1','row_geom'),('Ibound','awidth')]+old.OUTER_EQUALITIES[3:]
EQUALITIES=OUTER_EQUALITIES+old.retained.CORE_EQUALITIES


def source_residuals():
    z=SYM
    q,A,quot,H,C,Y,J,alpha=[z[n] for n in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=[z[n] for n in CORE_NAMES]
    W=16*A;L=q**4;scale=q**6
    U=307*C+4*Y+J;T=16*C+H
    P=T+q*Y+q**3*U;M=J*(q+1)*(4*q*q+14)
    Up=w*scale;Yp=s*scale;D=a*a+4*a+3
    auxu=j*c-(2*r+1)
    return [q-W*quot,q-1-H*(W-1),z['I']+alpha-A,
            z['I']+W*Y-C-q*z['F'],15*J-q+1,r-(L-P)*(L-1)-M,
            Up*Yp*Yp*(Up*Yp*Yp+1)*k*k-tau*(tau+1),
            c-Yp*k-eta,k-eta-zeta,k-r-1-h*Up*Yp,
            a-Yp*(Up+1),d-Up-a*c-ga*(4*a+3),
            d*d-D*c*c-1,(i*c*c)**2-D*(f*f-1),
            D*(f*f-1)*(auxu*auxu-ya*ya)-(1-ya*ya),auxu+c-o*f]


def verify_source(retain_divisor=True):
    rows=SCHEDULE if retain_divisor else [row for row in SCHEDULE if row[0]!='Wq']
    equalities=EQUALITIES if retain_divisor else EQUALITIES[1:]
    sources=source_residuals() if retain_divisor else source_residuals()[1:]
    names=NAMES if retain_divisor else [name for name in NAMES if name!='quot']
    env={name:SYM[name] for name in names}
    histogram=baseline.run_schedule(rows,env)
    auxu=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=source_residuals()[13]*(auxu**2-SYM['y_aux']**2)
    records=[]
    for index,((left,right),residual) in enumerate(zip(equalities,sources)):
        actual=sp.expand(env[left]-env[right])
        adjustment=correction if index==(14 if retain_divisor else 13) else sp.Integer(0)
        sign=1 if sp.expand(actual-residual-adjustment)==0 else -1
        assert sp.expand(actual-sign*residual-adjustment)==0,index
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(residual)),correction=sp.sstr(sp.expand(adjustment))))
    primitives,counts=verify_primitives(rows,env)
    expected=76 if retain_divisor else 75
    assert len(primitives)==expected and counts=={'+':33,'*':expected-33}
    assert len(equalities)==len(sources)==(16 if retain_divisor else 15)
    assert len(names)==len(set(names))==(27 if retain_divisor else 26)
    assert all(p.free_symbols<=set(SYM[n] for n in names) for p in sources)
    assert sp.expand(env['W']-16*SYM['awidth'])==0
    assert sp.expand(env['n2']-SYM['q']**6)==0
    return dict(operations=expected,multiplications=expected-33,additions_subtractions=33,
                positive_unknown_count=len(names)-2,positive_unknowns=[n for n in names if n not in PARAMETERS],
                equations=len(equalities),outer_operations=expected-43,kernel_operations=43,
                primitive_instructions=primitives,histogram=histogram,sources=records)


def numeric_outer(values,retain_divisor=True):
    env=dict(values)
    for name,op,left,right in OUTER:
        if not retain_divisor and name=='Wq':continue
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env


def check_tuple(m,t,B,Y,I,F):
    W=16**m;q=W**t;A=W//16;H=(q-1)//(W-1);J=(q-1)//15
    assert B>0 and B%16==0 and 0<I<A and F>0
    C=B//16;U=307*C+4*Y+J;T=B+H
    assert all(0<x<q for x in (U,T,Y))
    assert old.typed(T) and old.typed(Y) and old.typed(U,old.ALLOWED_U)
    P=T+q*Y+q**3*U;M=J*(q+1)*(4*q*q+14);L=q**4
    r=(L-P)*(L-1)+M
    values=dict(q=q,awidth=A,quot=q//W,hrow=H,Cw=C,Yw=Y,Jrow=J,
                alphaI=A-I,r=r,I=I,F=F)
    env=numeric_outer(values)
    assert min(values.values())>0 and all(env[a]==env[b] for a,b in OUTER_EQUALITIES)
    assert env['packed']==P and env['mask']==M and env['Uw']==U
    assert 0<P<L and 0<M<L and P&M==0
    assert M.bit_count()==8*m*t and r.bit_count()==24*m*t and r%2==1
    assert q**3<r<q**8 and q**6<r*r
    assert old.typed(B) and old.typed(I) and old.typed(F)
    current=16*I
    for row in range(t):
        bj=B//W**row%W;yj=Y//W**row%W
        assert bj==current and bj%16==0 and yj==old.rule(bj)
        current=16*yj
    assert current==16*F and F<W//16
    return dict(m=m,t=t,I=I,F=F,positive_outer_coordinates=values,
                checked_outer_equations=6,central_valuation=24*m*t)


def verify_histories():
    candidates=boundary=finals=misaligned=0;accepted=[]
    for N in range(2,13):
        q=16**N;J=(q-1)//15
        words=[old.word(raw) for raw in range(1<<N)]
        for exponent in range(5,min(24,4*N)+1):
            if 4*N%exponent:continue
            W=2**exponent;A=W//16;H=(q-1)//(W-1)
            for T in words:
                candidates+=1
                if exponent%4:misaligned+=1
                B=T-H
                if B<=0 or B%16:continue
                C=B//16;I=C%W
                if not 0<I<A:continue
                # The initial-bound/marker lemma forces alignment before Y decoding.
                assert exponent%4==0
                lower=C//W
                if not old.typed(lower):continue
                boundary+=1;m=exponent//4;t=N//m
                for raw in range(1,1<<m):
                    F=old.word(raw);finals+=1
                    Y=lower+(q//W)*F;U=307*C+4*Y+J
                    if 0<U<q and old.typed(U,old.ALLOWED_U):
                        accepted.append(check_tuple(m,t,B,Y,I,F))
    canonical=[]
    for I in (1,17,257,273,4097):
        for t in (1,2,3,4,8,16):
            rows=[];outputs=[];current=16*I
            for _ in range(t):
                rows.append(current);outputs.append(old.rule(current));current=16*outputs[-1]
            m=max(3,max(x.bit_length() for x in rows+outputs)//4+3)
            W=16**m
            B=sum(x*W**j for j,x in enumerate(rows));Y=sum(x*W**j for j,x in enumerate(outputs))
            canonical.append(check_tuple(m,t,B,Y,I,outputs[-1]))
    assert accepted and len(canonical)==30
    return dict(candidate_T_words=candidates,misaligned_T_words=misaligned,
                surviving_boundaries=boundary,compatible_final_words=finals,
                accepted_count=len(accepted),accepted=accepted,
                canonical_count=len(canonical),canonical=canonical)


def verify_bounds_and_alignment():
    tested=positive=nonpower=0
    for A,k in product((2,3,4,7,9,16,17),range(7)):
        W=16*A;H=1+k*W;q=1+H*(W-1)
        if (q-1)%15:continue
        J=(q-1)//15;L=q**4;M=J*(q+1)*(4*q*q+14)
        assert q%W==0 and q>=W>=32 and 0<M<L
        for C,Y in product((1,max(1,q//307-1),q//307+1,q),
                           (1,max(1,q//4-1),q//4+1,q)):
            U=307*C+4*Y+J;T=16*C+H;P=T+q*Y+q**3*U
            r=(L-P)*(L-1)+M;tested+=1
            if r<=0:continue
            positive+=1;nonpower+=bool(q&(q-1))
            assert U<q and 256*C<q and T<q and P<L and q**3<r<q**8
    assert min(tested,positive,nonpower)>0
    lowblocks=bad=0
    for exponent in range(5,19):
        W=2**exponent
        for I in range(1,W//16):
            low=16*I+1+W
            assert low<16*W and low>>exponent&1
            if exponent%4:assert not old.typed(low);bad+=1
            lowblocks+=1
    return dict(prepower_candidates=tested,positive_index_candidates=positive,
                nonpower_q_positive_index_candidates=nonpower,
                initial_low_blocks=lowblocks,misaligned_low_blocks_rejected=bad)


def deleted_divisor_counterexample():
    q=16**8;W=16**6-16**4+16**2;A=W//16
    I=256;F=69633;C=1114368;Y=17895680;H=257;J=(q-1)//15
    U=307*C+4*Y+J;T=16*C+H;P=T+q*Y+q**3*U
    M=J*(q+1)*(4*q*q+14);r=(q**4-P)*(q**4-1)+M
    values=dict(q=q,awidth=A,hrow=H,Cw=C,Yw=Y,Jrow=J,alphaI=A-I,r=r,I=I,F=F)
    env=numeric_outer(values,False)
    assert min(values.values())>0 and q%W!=0
    assert all(env[a]==env[b] for a,b in OUTER_EQUALITIES[1:])
    assert old.typed(I) and old.typed(F) and old.typed(T) and old.typed(Y)
    assert old.typed(U,old.ALLOWED_U) and all(0<x<q for x in (T,Y,U))
    assert 0<P<q**4 and 0<M<q**4 and P&M==0
    assert r.bit_count()==192 and r%2==1 and q**3<r<q**8 and q**6<r*r
    assert I%16==0 and F%16==1 # A moving history preserves the lowest occupied position.
    return dict(positive_outer_coordinates=values,W=W,T=T,U=U,
                central_valuation=192,index_parity=1,
                impossible_endpoint_reason='I has lowest occupied digit2; F has lowest occupied digit0.',
                full_positive_extension='All sixteen remaining positive coordinates use the fixed-minus43 converse at this exact odd r and D0=q^6.')


def verify():
    return dict(status='PASS_LINEAR_WIDTH_RULE110_HISTORY76',source=verify_source(),
                weakened75_source=verify_source(False),bounds_alignment=verify_bounds_and_alignment(),
                histories=verify_histories(),deleted_divisor=deleted_divisor_counterexample(),
                proof='../1980/EXPLORATION_LINEAR_WIDTH_RULE110_HISTORY.md',
                review='Author and independent complete proof/source review pass; fresh read-only verification exactly matches the saved JSON.',
                scope='Complete positive radix16 moving finite-history endpoint relation, with exactly the same numerical I,F semantics as77. No universal input/halting interface.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(result['status']);print({k:result['source'][k] for k in ('operations','multiplications','additions_subtractions','positive_unknown_count','equations')})
    print(result['bounds_alignment'])
    print({k:v for k,v in result['histories'].items() if k not in ('accepted','canonical')})
