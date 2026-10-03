"""All-length rank obstruction to two independent zero-code Rule110 carries."""
import argparse
from itertools import product
import json
from pathlib import Path
import sympy as sp


def symbolic_matrix():
    R,C=sp.symbols('R C',positive=True)
    uA,uB,uC,vA,vB,vC,vD=sp.symbols('uA uB uC vA vB vC vD')
    matrix=sp.Matrix([[uA,C,vA+R*vB,(R+1)*C],
                      [uB,C,vC+R*vD-vB,R*C],
                      [uC,C,(R-1)*vD,(R-1)*C]])
    left=sp.Matrix([[1,-2,1]])
    relation=(left*matrix).applyfunc(sp.expand)
    assert (relation-sp.Matrix([[uA-2*uB+uC,0,vA-2*vC+(R+2)*vB-(R+1)*vD,0]])).applyfunc(sp.expand)==sp.zeros(1,4)
    assert matrix.extract([0,1],[1,3]).det()==-C*C
    u,v=sp.symbols('u v')
    collapsed=matrix.subs({uA:u,uB:u,uC:u,vA:v,vB:v,vC:v,vD:v})
    assert (collapsed[0,:]-collapsed[1,:]).applyfunc(sp.expand)==sp.Matrix([[0,0,v,C]])
    app_relation=relation[2]
    assert sp.expand(app_relation-((R+1)*(vB-vD)-(2*vC-vA-vB)))==0
    return dict(matrix=[[str(v) for v in matrix.row(i)] for i in range(3)],
                coefficient_coordinates=['read0-read1','read1','append0-append1','append1'],
                nonzero_minor='-C^2',forced_left_relation=[1,-2,1],
                state_elimination=['B=-append_weight(P_B)','C_state=-append_weight(P_D)'],
                collapse='All three encoded states coincide in every coefficient direction of a rank-two matrix')


def boolean_words(length):
    return [sum(bit*3**j for j,bit in enumerate(bits)) for bits in product((0,1),repeat=length)]


def finite_checks():
    rows=[]
    for length in range(1,5):
        R=3**length;H=(R-1)//2
        words=boolean_words(length);word_set=set(words)
        read_cases=append_cases=read_equalities=append_equalities=0
        for code in range(1,R):
            split=[u for u in words if code-u in word_set]
            for uA,uB,uC in product(split,repeat=3):
                condition=uA-2*uB+uC==0
                assert condition==(uA==uB==uC)
                read_cases+=1;read_equalities+=condition
            for vA,vB,vC,vD in product(split,repeat=4):
                condition=vA-2*vC+(R+2)*vB-(R+1)*vD==0
                assert condition==(vA==vB==vC==vD)
                assert abs(2*vC-vA-vB)<=2*H<R+1
                append_cases+=1;append_equalities+=condition
        rows.append(dict(length=length,read_split_triples=read_cases,append_split_quadruples=append_cases,
                         admitted_read_relations=read_equalities,admitted_append_relations=append_equalities))
    # A direct rank-three realization: the established00/12 code has only one coefficient direction.
    R=9;code=7
    uA,uB,uC=3,4,4
    vA,vB,vC,vD=4,4,3,3
    matrix=sp.Matrix([[uA,code,vA+R*vB,(R+1)*code],
                      [uB,code,vC+R*vD-vB,R*code],
                      [uC,code,(R-1)*vD,(R-1)*code]])
    coefficients=sp.Matrix([-84,56,-7,2])
    assert matrix*coefficients==sp.zeros(3,1) and matrix.rank()==3
    assert -((-7)*vB+2*code)==14 and -((-7)*vD+2*code)==7
    return dict(all_split_domains=rows,existing_code_rank=3,existing_code_nullity=1,
                existing_states=[0,14,7],
                scope='Finite checks supplement the all-length digit and interval proofs')


def verify():
    return dict(status='PASS_TWO_CARRY_ZERO_CODE_RANK_OBSTRUCTION',symbolic=symbolic_matrix(),finite=finite_checks(),
                theorem='Any direct distinct-three-state Rule110 embedding with zero code and one common nonzero block code has at most one independent affine carry coefficient direction',
                scope='All block lengths, common Boolean rail realizations; does not exclude state refinement or different local relations',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],finite=result['finite'],scope=result['scope']),indent=2))
