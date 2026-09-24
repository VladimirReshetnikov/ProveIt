#!/usr/bin/env python3
"""Complete generic four-cell cyclic70 arithmetic, with fixed relation constants.

This checks the pointwise q,P,C relation with positive witnesses. Marker
occurrence and a fixed raw-input universal compiler are not included.
Numerical receipts store bit lengths rather than enormous fixed numerals.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import random
import sys
import sympy as sp

import explore_multibit_affine_cell as compiler
import explore_rule110_cyclic_short_mask as retained
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives

OUT=Path(__file__).with_suffix('.json')
PARAMETERS=list(retained.PARAMETERS)
OUTER_NAMES=list(retained.OUTER_NAMES)
CORE_NAMES=list(retained.CORE_NAMES)
NAMES=PARAMETERS+OUTER_NAMES+CORE_NAMES
CONSTANT_NAMES=['B','DL','DC','DR','DY','G0','MC','MF']
SYM={name:sp.Symbol(name) for name in NAMES+CONSTANT_NAMES}
OUTER=[
    ('qm1','-','q',1),('repunit','*','Bm1','Jrep'),
    ('Pv','*','P','v'),('Pm1','-','P',1),('alignment','*','Bm1','align'),
    ('bounded','+','C','alpha'),
    ('kp','*','Kcoef','P'),('kinner','+','DC','kp'),('innerC','*','kinner','C'),
    ('transport_gap','-','innerC','F'),('Pgap','*','P','transport_gap'),
    ('DLC','*','DL','C'),('GJ','*','G0','Jrep'),
    ('local_sum','+','Pgap','DLC'),('local_lhs','+','local_sum','GJ'),
    ('local_rhs','*','zquot','qm1'),
    ('Lbig','*','q','q'),('n2','*','Lbig','q'),
    ('qF','*','q','F'),('packed','+','C','qF'),
    ('qMF','*','q','MF'),('mask_factor','+','MC','qMF'),('mask','*','mask_factor','Jrep'),
    ('gap','-','Lbig','packed'),('Lm1','-','Lbig',1),
    ('rproduct','*','gap','Lm1'),('r_lhs','+','rproduct','mask'),
]
CORE=list(retained.CORE)
SCHEDULE=OUTER+CORE
OUTER_EQUALITIES=[('repunit','qm1'),('Pv','q'),('alignment','Pm1'),
                  ('bounded','q'),('local_lhs','local_rhs'),('r','r_lhs')]
EQUALITIES=OUTER_EQUALITIES+retained.previous.retained.retained.CORE_EQUALITIES


def fixed_environment(symbols):
    env=dict(symbols)
    env['Bm1']=env['B']-1
    env['Kcoef']=env['DR']+env['B']*env['DY']
    return env


def source_residuals():
    z=SYM
    q,P,C=[z[name] for name in PARAMETERS]
    v,J,align,F,alpha,zquot=[z[name] for name in OUTER_NAMES]
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,ya=[z[name] for name in CORE_NAMES]
    B,DL,DC,DR,DY,G0,MC,MF=[z[name] for name in CONSTANT_NAMES]
    L=q*q;scale=q**3;S=C+q*F;M=(MC+q*MF)*J
    X=w*scale;Y=s*scale;Delta=a*a+4*a+3;auxu=j*c-(2*r+1)
    K=DL+P*(DC+(DR+B*DY)*P)
    return [(B-1)*J-q+1,P*v-q,(B-1)*align-P+1,C+alpha-q,
            K*C+G0*J-P*F-zquot*(q-1),r-(L-S)*(L-1)-M,
            X*Y*Y*(X*Y*Y+1)*k*k-tau*(tau+1),
            c-Y*k-eta,k-eta-zeta,k-r-1-h*X*Y,
            a-Y*(X+1),d-X-a*c-ga*(4*a+3),d*d-Delta*c*c-1,
            (i*c*c)**2-Delta*(f*f-1),
            Delta*(f*f-1)*(auxu*auxu-ya*ya)-(1-ya*ya),auxu+c-o*f]


def verify_source():
    env=fixed_environment(SYM);histogram=baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();u=SYM['j']*SYM['c']-(2*SYM['r']+1)
    correction=sources[13]*(u*u-SYM['y_aux']**2);records=[]
    for index,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if index==14 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,index
        records.append(dict(index=index,equality=[left,right],source_sign=sign,
                            source=sp.sstr(sp.expand(source)),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=verify_primitives(SCHEDULE,env)
    assert len(OUTER)==27 and len(CORE)==43 and len(primitives)==70
    assert counts=={'+':30,'*':40}
    assert Counter(row[1] for row in OUTER)=={'*':15,'+':7,'-':5}
    assert len(EQUALITIES)==len(sources)==16
    assert len(NAMES)==len(set(NAMES))==26 and len(OUTER_NAMES+CORE_NAMES)==23
    assert sp.expand(env['n2']-SYM['q']**3)==0
    assert all(p.free_symbols<=set(SYM.values()) for p in sources)
    assert set(NAMES)<=({x for row in SCHEDULE for x in row[2:]}
                        |{x for pair in EQUALITIES for x in pair})
    return dict(operations=70,multiplications=40,additions_subtractions=30,
                outer_operations=27,kernel_operations=43,parameters=PARAMETERS,
                positive_unknown_count=23,positive_unknowns=OUTER_NAMES+CORE_NAMES,
                positive_coordinates_including_parameters=26,equations=16,
                fixed_constant_names=CONSTANT_NAMES,
                fixed_numeral_aliases={'Bm1':'B-1','Kcoef':'DR+B*DY'},
                primitive_instructions=primitives,histogram=histogram,sources=records,
                kernel_scale='q^3; no pre-power square-scale assumption',
                kernel_sign='fixed minus; actual packed r is odd',
                ledger={'geometry':5,'bound':1,'local_positive_quotient':10,'packing':11})


def constants(cc):
    DL,DC,DR,DY=cc.convolution
    return dict(B=cc.cell_radix,DL=DL,DC=DC,DR=DR,DY=DY,G0=cc.guard,
                MC=cc.state_mask,MF=cc.field_mask)


def numeric_outer(values,const):
    env=fixed_environment({**const,**values})
    for name,op,left,right in OUTER:
        aa=env[left] if isinstance(left,str) else left;bb=env[right] if isinstance(right,str) else right
        env[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
    return env


def digest_integer(value):
    assert value>=0
    return hashlib.sha256(value.to_bytes(max(1,(value.bit_length()+7)//8),'big')).hexdigest()


def check_cyclic(cc,allowed,genuine,fill_mode,hh):
    N=len(genuine);k=cc.state_bits;m=cc.clauses;B=cc.cell_radix
    seed=1009+hh+97*fill_mode+sum((i+1)*sum((j+1)*b for j,b in enumerate(row)) for i,row in enumerate(genuine))
    rng=random.Random(seed)
    rows=[tuple(bits)+tuple(0 if fill_mode==0 else 1 if fill_mode==1 else rng.randrange(2)
                           for _ in range(m-k)) for bits in genuine]
    cells=[cc.cell(row) for row in rows]
    q=1<<(cc.cell_bits*N);P=1<<(cc.cell_bits*hh);D=q-1;J=D//(B-1)
    powers=[1<<(cc.cell_bits*i) for i in range(N)]
    pack=lambda values:sum(value*power for value,power in zip(values,powers))
    C=pack(cells)
    LL=pack([cells[(i+hh)%N] for i in range(N)])
    RR=pack([cells[(i-hh)%N] for i in range(N)])
    YY=pack([cells[(i-hh-1)%N] for i in range(N)])
    const=constants(cc);DL,DC,DR,DY=cc.convolution;G0=cc.guard
    F=G0*J+DL*LL+DC*C+DR*RR+DY*YY
    fields=[];actual=True
    for i in range(N):
        positions=((i+hh)%N,i,(i-hh)%N,(i-hh-1)%N)
        projected=tuple(bit for pos in positions for bit in genuine[pos])
        raw=G0+sum(coef*cells[pos] for coef,pos in zip(cc.convolution,positions))
        assert 0<raw<=B-2 and (raw&cc.field_mask==0)==(projected in allowed)
        fields.append(raw);actual &= projected in allowed
    assert F==pack(fields) and 0<F<D and 0<=C<q and C%2==0
    assert C&(cc.state_mask*J)==0
    S=C+q*F;L=q*q;M=(cc.state_mask+q*cc.field_mask)*J
    r=(L-S)*(L-1)+M
    assert 0<S<L and 0<M<L-1 and r>=q*q and r<q**4 and r*r>q**3
    assert M.bit_count()==cc.cell_bits*N and r%2==1
    assert (r.bit_count()==3*cc.cell_bits*N)==(S&M==0)==actual
    K=DL+P*(DC+(DR+B*DY)*P)
    z,rem=divmod(K*C+G0*J-P*F,D);assert rem==0
    kL=(P*LL-C)//D;kR=(P*C-RR)//D;kY=(B*P*C-YY)//D;align=(P-1)//(B-1)
    assert 0<=kL<P and kR>=0 and kY>=0
    assert z==P*(DR*kR+DY*kY)-DL*kL-G0*align
    # Always compare the complete outer residual, even if a supplied
    # positive coordinate would fail for this invalid word.
    values=dict(q=q,P=P,C=C,v=q//P,Jrep=J,align=align,F=F,
                alpha=q-C,zquot=z,r=r)
    env=numeric_outer(values,const)
    assert all(env[aa]==env[bb] for aa,bb in OUTER_EQUALITIES)
    if actual:
        assert all(any(row) for row in genuine)
        assert min(cells)>=2 and C>=2*J and kY>=2*P
        assert 0<DL<B and 0<G0<B-1 and DY>=1
        assert z>2*P*P-B*(P-1)>0
        assert min(values.values())>0
    valid_codes={tuple(row[s*k:(s+1)*k]) for row in allowed for s in range(4)}
    return dict(accepted=bool(actual),all_valid_projected_states=all(tuple(row) in valid_codes for row in genuine),
                zero_projected_cell=any(not any(row) for row in genuine),
                zero_projected_word=all(not any(row) for row in genuine),
                zero_numeric_C=C==0,quotient_sign='positive' if z>0 else 'negative' if z<0 else 'zero',
                q_bits=q.bit_length(),r_bits=r.bit_length(),z_bits=abs(z).bit_length(),
                C_digest=digest_integer(C),F_digest=digest_integer(F),r_digest=digest_integer(r))


def verify_compiled_example(name,k,allowed,max_exhaustive_length,extra_random=False,curated_cycle=False):
    cc=compiler.compile_cells(4,k,allowed)
    assert (0,)*(4*k) not in allowed
    assert all(all(any(row[s*k:(s+1)*k]) for s in range(4)) for row in allowed)
    const=constants(cc);B=cc.cell_radix
    assert B>=16 and 0<const['MC']<=B-2 and 0<const['MF']<=B-2
    assert const['MC']%2==1 and const['MF']%2==0
    assert const['MC'].bit_count()+const['MF'].bit_count()==cc.cell_bits
    cases=accepted=invalid_zero_cells=all_zero_projections=zero_C=valid_state_cases=transition_rejections=0
    signs=Counter();valid_signs=Counter();samples=[];directional_cases=[]
    max_q_bits=max_r_bits=0
    domain=tuple(product((0,1),repeat=k))
    trials=[]
    for N in range(1,max_exhaustive_length+1):
        for word in product(domain,repeat=N):
            for hh in range(1,N+1):
                for fill in range(3):trials.append((word,fill,hh))
    if extra_random:
        rng=random.Random(2309)
        for _ in range(4):
            word=tuple(rng.choice(domain) for _ in range(3))
            for hh in (1,3):
                for fill in (0,2):trials.append((word,fill,hh))
    if curated_cycle:
        assert k==2
        for hh in (1,3):
            for fill in range(3):trials.append((((0,1),(1,0),(1,1)),fill,hh))
    for word,fill,hh in trials:
        record=check_cyclic(cc,allowed,word,fill,hh)
        cases+=1;accepted+=record['accepted'];signs[record['quotient_sign']]+=1
        invalid_zero_cells+=record['zero_projected_cell'];all_zero_projections+=record['zero_projected_word']
        valid_state_cases+=record['all_valid_projected_states']
        transition_rejections+=record['all_valid_projected_states'] and not record['accepted']
        zero_C+=record['zero_numeric_C'];max_q_bits=max(max_q_bits,record['q_bits']);max_r_bits=max(max_r_bits,record['r_bits'])
        if record['accepted']:valid_signs[record['quotient_sign']]+=1
        if curated_cycle and word==((0,1),(1,0),(1,1)):
            assert record['all_valid_projected_states'] and record['accepted']==(hh==1)
            directional_cases.append(dict(stride=hh,dummy_mode=fill,accepted=record['accepted']))
        if len(samples)<4 or (record['accepted'] and not any(x['accepted'] for x in samples)):
            samples.append(dict(length=len(word),stride=hh,dummy_mode=fill,projected_word=[list(z) for z in word],**record))
    assert cases>0 and accepted>0 and invalid_zero_cells>0 and all_zero_projections>0
    assert valid_signs=={'positive':accepted}
    return dict(name=name,state_bits=k,allowed_four_cell_tuples=len(allowed),clauses=cc.clauses,
                dummy_bits_per_cell=cc.clauses-k,inner_bits=cc.inner_bits,cell_bits=cc.cell_bits,
                fixed_constant_bit_lengths={name:value.bit_length() for name,value in const.items()},
                state_mask_weight=cc.state_mask.bit_count(),field_mask_weight=cc.field_mask.bit_count(),
                cyclic_cases=cases,accepted=accepted,invalid_zero_state_cases=invalid_zero_cells,
                valid_projected_state_cases=valid_state_cases,genuine_transition_rejections=transition_rejections,
                all_zero_projected_word_cases=all_zero_projections,zero_numeric_C_cases=zero_C,
                quotient_signs=dict(signs),accepted_quotient_signs=dict(valid_signs),
                max_q_bits=max_q_bits,max_r_bits=max_r_bits,samples=samples,directional_cases=directional_cases,
                full_packed_Pell_tuples_materialized=False)


def verify_prebounds():
    candidates=positive=nonpower=0
    for B in (16,32,256):
        for align,v0 in product(range(1,6),range(4)):
            P=1+(B-1)*align;v=1+(B-1)*v0;q=P*v;J=(q-1)//(B-1);L=q*q
            for MC,MF in product((1,B-2),repeat=2):
                M=(MC+q*MF)*J
                assert L-1-M==J*((B-1-MF)*q+B-1-MC)>0
                for C,F in product((1,q//2,q-2),(1,q-1,q,q+1)):
                    candidates+=1;alpha=q-C;S=C+q*F;r=(L-S)*(L-1)+M
                    if r<=0:continue
                    positive+=1;nonpower+=bool(q&(q-1))
                    assert 0<C<q and F<q and 0<S<L
                    assert r>=q*q>=256 and r<q**4 and q**3<r*r
                    assert q**6>2*r+1 and 8*r<q**6
    return dict(candidates=candidates,positive_index_cases=positive,nonpower_q_cases=nonpower,
                mask_constants_tested='MC,MF independently at1 andB-2; only range hypotheses are used')


def verify_marked_source():
    symbols={**SYM,'Tmarker':sp.Symbol('Tmarker'),'CM':sp.Symbol('CM')}
    rows=SCHEDULE+[('Bmarker_tail','*','B','Tmarker'),('marked_rhs','+','CM','Bmarker_tail')]
    equalities=EQUALITIES+[('C','marked_rhs')]
    env=fixed_environment(symbols);baseline.run_schedule(rows,env)
    sources=source_residuals()+[symbols['C']-symbols['CM']-symbols['B']*symbols['Tmarker']]
    u=symbols['j']*symbols['c']-(2*symbols['r']+1)
    correction=sources[13]*(u*u-symbols['y_aux']**2)
    for index,((left,right),source) in enumerate(zip(equalities,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if index==14 else sp.Integer(0)
        assert (sp.expand(actual-source-adjust)==0
                or (adjust==0 and sp.expand(actual+source)==0)),index
    primitives,counts=verify_primitives(rows,env)
    assert len(primitives)==72 and counts=={'+':31,'*':41}
    unknowns=NAMES+['Tmarker']
    assert len(unknowns)==len(set(unknowns))==27 and len(sources)==17
    return dict(operations=72,multiplications=41,additions_subtractions=31,
                positive_unknown_count=27,positive_unknowns=unknowns,parameters=[],equations=17,
                base_schedule_is_unchanged_70_prefix=True,primitive_instructions=primitives,
                equalities=equalities,extra_source='C-CM-B*Tmarker=0',
                marker_constant='CM is the fixed genuine marker state code with all dummy bits zero',
                designated_marker_specialization='Enc(marker)=(1,0,...,0) gives CM=2',
                scope='Separate marked existence extension with q,P,C existential; constants depend on the fixed relation and marker')


def verify_marked_examples():
    valid=((1,0),(0,1),(1,1))
    examples=[(1,frozenset({(1,1,1,1)}),((1,),)),
              (2,frozenset(sum(states,()) for states in product(valid,repeat=4)),valid)]
    cases=repetitions=rotations=dummy_reset_rejections=0;records=[]
    for k,allowed,alphabet in examples:
        cc=compiler.compile_cells(4,k,allowed);B=cc.cell_radix;marker=alphabet[0]
        zero_dummy=(0,)*(cc.clauses-k);CM=cc.cell(marker+zero_dummy)
        assert CM==2
        for N in (1,2,3):
            original=tuple(alphabet[(i+1)%len(alphabet)] for i in range(N))
            original=original[:-1]+(marker,)
            before=check_cyclic(cc,allowed,original,2,1)
            assert before['accepted']
            anchor=original.index(marker)
            rotated=original[anchor:]+original[:anchor];rotations+=bool(anchor)
            if N==1:rotated=rotated*2;repetitions+=1
            after=check_cyclic(cc,allowed,rotated,0,1)
            assert after['accepted']
            C=sum(cc.cell(state+zero_dummy)*B**i for i,state in enumerate(rotated))
            Tmarker,remainder=divmod(C-CM,B)
            assert remainder==0 and Tmarker>0 and C==CM+B*Tmarker
            assert digest_integer(C)==after['C_digest']
            # The marker equality specifies the entire low cell, so a
            # nonzero dummy bit at the marker must first be reset.
            if cc.clauses>k:
                changed_marker=cc.cell(marker+(1,)+(0,)*(cc.clauses-k-1))
                assert 0<changed_marker-CM<B and (changed_marker-CM)%B!=0
                dummy_reset_rejections+=1
            records.append(dict(state_bits=k,original_length=N,original_marker_position=anchor,
                                final_length=len(rotated),stride=1,marker_bits=CM.bit_length(),
                                positive_tail_bits=Tmarker.bit_length(),C_digest=after['C_digest']))
            cases+=1
    return dict(cases=cases,length_one_repetitions=repetitions,nontrivial_rotations=rotations,
                noncanonical_dummy_marker_codes_rejected=dummy_reset_rejections,records=records,
                scope='Rotate a genuine marker to0, reset all dummy bits, repeat length1 to obtain positive tail; no giant Pell tuples')


def verify():
    one_allowed=frozenset({(1,1,1,1)})
    valid=((0,1),(1,0),(1,1))
    multi_allowed=frozenset(sum(states,()) for states in product(valid,repeat=4))
    next_left_allowed=frozenset(left+center+right+left for left,center,right in product(valid,repeat=3))
    examples=[verify_compiled_example('one-bit singleton alphabet',1,one_allowed,6),
              verify_compiled_example('two-bit three-symbol validity relation',2,multi_allowed,2,extra_random=True),
              verify_compiled_example('two-bit directional next=left relation',2,next_left_allowed,2,
                                      extra_random=True,curated_cycle=True)]
    assert examples[2]['genuine_transition_rejections']>0 and len(examples[2]['directional_cases'])>=6
    return dict(status='PASS_MULTIBIT_CYCLIC70',source=verify_source(),prepower_bounds=verify_prebounds(),
                examples=examples,pell=retained.previous.verify_pell_components(),
                marked_extension={'source':verify_marked_source(),'checks':verify_marked_examples()},
                proof='../1980/EXPLORATION_MULTIBIT_CYCLIC_CERTIFICATE.md',
                universal_certificate_improvement=False,
                scope='Complete positive generic four-cell cyclic relation in supplied q,P,C, for the fixed multi-bit compiler and nonzero valid state codes; no marker or raw-input universal compiler')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert json.loads(json.dumps(result))==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],'operations;',
          [(row['name'],row['cyclic_cases'],row['accepted']) for row in result['examples']])
