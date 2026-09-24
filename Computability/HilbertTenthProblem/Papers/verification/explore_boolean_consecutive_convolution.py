#!/usr/bin/env python3
"""Conditional 10-operation consecutive-stride Boolean CA congruence.

The source is one integer equality with a strictly positive quotient.
Boolean typing, finite-width/power geometry, and every universal
input/marker interface are deliberately unpriced.
Run normally to compare the receipt; use --write to create it.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import sys
import sympy as sp

from explore_boolean_affine_mask import compile_relation

OUT=Path(__file__).with_suffix('.json')
SCHEDULE=[
    ('aP','*','a','P'),
    ('inner','-','aP','cC'),
    ('Pinner','*','P','inner'),
    ('H','-','Pinner','cL'),
    ('HC','*','H','C'),
    ('PF','*','P','F'),
    ('left','+','PF','HC'),
    ('cJ','*','cstar','J'),
    ('wD','*','w','D'),
    ('right','+','cJ','wD'),
]


def verify_source():
    names='B c0 cL cC cR cY P C F J w D'.split()
    symbols=dict(zip(names,sp.symbols(' '.join(names))))
    env=dict(symbols)
    env['a']=symbols['B']*symbols['cY']-symbols['cR']
    env['cstar']=symbols['c0']+symbols['cY']
    primitives=[]
    for target,operation,left,right in SCHEDULE:
        if operation=='*':
            env[target]=env[left]*env[right]
            primitive=[left,'*',right,target]
        elif operation=='+':
            env[target]=env[left]+env[right]
            primitive=[left,'+',right,target]
        else:
            assert operation=='-'
            env[target]=env[left]-env[right]
            primitive=[target,'+',right,left]
        a,op,b,result=primitive
        assert sp.expand((env[a]*env[b] if op=='*' else env[a]+env[b])-env[result])==0
        primitives.append(primitive)
    s=symbols
    K=s['cL']+s['cC']*s['P']+(s['cR']-s['B']*s['cY'])*s['P']**2
    source=s['P']*s['F']-K*s['C']-(s['c0']+s['cY'])*s['J']-s['w']*s['D']
    assert sp.expand(env['H']+K)==0
    assert sp.expand(env['left']-env['right']-source)==0
    counts=Counter(row[1] for row in SCHEDULE)
    assert len(SCHEDULE)==10 and counts=={'*':6,'+':2,'-':2}
    return dict(operations=10,multiplications=6,additions=4,
                primitive_instructions=primitives,equality=['left','right'],
                source_residual=sp.sstr(sp.expand(source)),
                fixed_numerals={'a':'B*cY-cR','cstar':'c0+cY'},
                supplied_geometry='D=q-1, J=(q-1)/(B-1), P=B^h',
                quotient_domain='w is strictly positive; no signed-quotient adapter is needed')


def allowed_for_rule(rule):
    assert 0<=rule<256 and rule&1==0
    return frozenset((l,c,r,1-((rule>>(4*l+2*c+r))&1))
                     for l,c,r in product((0,1),repeat=3))


def verify():
    rule_records=[]
    scalar_cases=cyclic_cases=accepted=0
    quotient_signs=Counter()
    positive_intermediate_checks=0
    for rule in range(0,256,2):
        allowed=allowed_for_rule(rule)
        compiled=compile_relation(4,allowed,zero_last=True)
        B=compiled.cell_radix
        c0=compiled.constant
        cL,cC,cR,cY=compiled.coefficients
        assert c0>0 and min(compiled.coefficients)>0
        G=compiled.clause_radix**len(compiled.forbidden)
        coefficient_bound=(G-1)//(compiled.clause_radix-1)
        assert compiled.clause_radix==8 and len(compiled.forbidden)==8
        assert B==2*G and max(compiled.coefficients)<=coefficient_bound<B//2
        assert c0>=G-coefficient_bound and B*c0>c0+cY
        a=B*cY-cR
        assert a>0
        scalar={}
        for z in product((0,1),repeat=4):
            F=compiled.evaluate(z)
            assert 1<=F<=B-2
            assert (F&compiled.mask==0)==(z in allowed)
            scalar[z]=F
            scalar_cases+=1
        rule_cases=rule_accepted=0
        for N in range(1,7):
            q=B**N
            D=q-1
            J=D//(B-1)
            powers=[B**i for i in range(N)]
            packed_mask=compiled.mask*J
            for word in range(1<<N):
                bits=[(word>>i)&1 for i in range(N)]
                C=sum(bit*power for bit,power in zip(bits,powers))
                for h in range(1,N+1):
                    P=B**h
                    Q=B*P
                    left=[bits[(i+h)%N] for i in range(N)]
                    right=[bits[(i-h)%N] for i in range(N)]
                    nxt=[bits[(i-h-1)%N] for i in range(N)]
                    cells=[(left[i],bits[i],right[i],1-nxt[i]) for i in range(N)]
                    F=sum(scalar[cell]*powers[i] for i,cell in enumerate(cells))
                    assert 0<F<D
                    K=(cC-a*P)*P+cL
                    assert K==cL+P*(cC+cR*P-cY*Q)
                    numerator=K*C+(c0+cY)*J-P*F
                    z,remainder=divmod(numerator,D)
                    assert remainder==0 and P*F+z*D==K*C+(c0+cY)*J
                    quotient_signs['positive' if z>0 else 'negative' if z<0 else 'zero']+=1
                    w=-z
                    assert w>0 and a*P-cC>0 and -K>0
                    assert P*F-K*C==(c0+cY)*J+w*D
                    env={'a':a,'P':P,'cC':cC,'cL':cL,'C':C,
                         'F':F,'cstar':c0+cY,'J':J,'w':w,'D':D}
                    for target,operation,aa,bb in SCHEDULE:
                        env[target]=(env[aa]*env[bb] if operation=='*' else
                                     env[aa]+env[bb] if operation=='+' else env[aa]-env[bb])
                        assert env[target]>=0
                        assert env[target]>0 or (target=='HC' and C==0)
                        positive_intermediate_checks+=1
                    assert env['left']==env['right']
                    actual=all(cell in allowed for cell in cells)
                    via_mask=F&packed_mask==0
                    assert actual==via_mask
                    # Every point in a small pullback rectangle obeys exactly
                    # the same local formula; the proof handles all Z^2.
                    for xx,tt in ((0,0),(1,0),(0,1),(2,3)):
                        i=(-h*xx-(h+1)*tt)%N
                        assert cells[i]==(
                            bits[(-h*(xx-1)-(h+1)*tt)%N],
                            bits[i],
                            bits[(-h*(xx+1)-(h+1)*tt)%N],
                            1-bits[(-h*xx-(h+1)*(tt+1))%N])
                    cyclic_cases+=1
                    rule_cases+=1
                    accepted+=actual
                    rule_accepted+=actual
        rule_records.append(dict(rule=rule,cyclic_cases=rule_cases,accepted=rule_accepted,
                                 scalar_min=min(scalar.values()),scalar_max=max(scalar.values())))
    assert len(rule_records)==128 and cyclic_cases==82176 and scalar_cases==2048
    return dict(status='PASS',scope='Conditional local cyclic congruence and Boolean truth equivalence only',
                universal_certificate_improvement=False,source=verify_source(),
                quiescent_binary_radius1_rules=128,scalar_assignments=scalar_cases,
                cell_radix=1<<25,word_lengths=[1,6],strides='h=1,...,N; next shift h+1',
                cyclic_cases=cyclic_cases,accepted_cyclic_words_and_strides=accepted,
                positive_quotient_cases=cyclic_cases,
                nonnegative_intermediate_checks=positive_intermediate_checks,
                signed_derivation_quotient_sign_counts=dict(sorted(quotient_signs.items())),rules=rule_records,
                unpaid=['q and P power/alignment geometry','J and D formation','Boolean typing and field bounds',
                        'repeated mask formation and its arithmetic enforcement',
                        'nonzero-domain and marker/input/target interface','cyclic-quotient completeness for the actual computational model'])


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'local operations;',
          result['cyclic_cases'],'cyclic cases;',result['positive_quotient_cases'],'positive quotients')
