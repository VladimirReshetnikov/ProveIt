"""Ten paid gates load the primary C2 query from Q=8**(32*x).

The power relation is an explicit external interface of this module.
One positive program coefficient records the fixed primary program word.
No positional encoding or rational coefficient is an unpaid arithmetic gate.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import tseytin_group_completion_obstruction as primary

BASE=8
B=BASE**32
DENOMINATOR=B*B-1
CODES={c:i+1 for i,c in enumerate('abcde')}


def raw(word):
    n=0
    for c in word:n=BASE*n+CODES[c]
    return n


def encode(word):return BASE**len(word)+raw(word)


def code_for_group(rank):
    assert type(rank) is int and rank>=2
    result={'alpha':1,'beta':0,1:2,-1:3,2:31,-2:63}
    remaining=[x for i in range(3,rank+1) for x in (i,-i)]
    result.update(zip(remaining,range(64,64+len(remaining))))
    assert len(set(result.values()))==len(result)
    return result


def program_word(rank,relators):
    assert type(rank) is int and rank>=2
    assert all(type(x) is int and 1<=abs(x)<=rank for r in relators for x in r)
    special=[tuple(r) for r in relators]+[(i,-i) for i in range(1,rank+1)]+[(-i,i) for i in range(1,rank+1)]
    word=('alpha','alpha')
    for r in special:word+=r+('alpha',)
    return primary.phi(word,code_for_group(rank)).translate(str.maketrans('ab','cd'))


def query_word(S,x):
    assert set(S)<=set('cd') and type(x) is int and x>0
    return S+primary.phi(('beta',)+primary.commutator_input(x)+('beta',),code_for_group(2))


def add(a,b):
    r=dict(a)
    for k,v in b.items():r[k]=r.get(k,Fraction(0))+v
    return {k:v for k,v in r.items() if v}


def multiply(a,b):
    r={}
    for k,v in a.items():
        for j,w in b.items():r[k+j]=r.get(k+j,Fraction(0))+v*w
    return {k:v for k,v in r.items() if v}


def coefficients():
    """Exact symbolic concatenation; Fraction is only a compile-time proof tool."""
    fixed=lambda word:({0:Fraction(BASE**len(word))},{0:Fraction(raw(word))})
    def repeated(length):
        c=Fraction(raw('a'+'b'*(length-1)),BASE**length-1)
        return {length//32:Fraction(1)},{length//32:c,0:-c}
    blocks=[fixed('a'),repeated(64),fixed('abb'),repeated(32),fixed('abb'),
            repeated(64),fixed('abbb'),repeated(32),fixed('abbb'),fixed('aa')]
    scale={0:Fraction(1)};value={}
    for s,v in blocks:scale=multiply(scale,s);value=add(multiply(value,s),v)
    assert scale=={6:BASE**17}
    coeff=[DENOMINATOR*value.get(i,0) for i in range(7)]
    assert all(v.denominator==1 for v in coeff)
    coeff=list(map(int,coeff))
    assert coeff[2]==coeff[5]==0 and coeff[6]>0
    assert all(coeff[i]<0 for i in (0,1,3,4))
    return coeff


COEFFICIENTS=coefficients()
LEADING_SCALE=DENOMINATOR*BASE**17


def program_parameter(S):
    assert S and set(S)<=set('cd')
    value=LEADING_SCALE*encode(S)+COEFFICIENTS[6]
    assert value>0
    return value


def build():
    c=COEFFICIENTS
    source=[('query_Q2','*','Q','Q'),
            ('query_leading','*','program_A','query_Q2'),
            ('query_degree4','-', 'query_leading',-c[4]),
            ('query_times_Q','*','query_degree4','Q'),
            ('query_degree3','-','query_times_Q',-c[3]),
            ('query_times_Q2','*','query_degree3','query_Q2'),
            ('query_degree1','-','query_times_Q2',-c[1]),
            ('query_last_product','*','query_degree1','Q'),
            ('query_numerator','-','query_last_product',-c[0]),
            ('query_scaled_word','*',DENOMINATOR,'word')]
    return dict(source=source,parameters=['program_A','Q','word'],auxiliaries=[],
        comparisons=[('query_numerator','query_scaled_word')],
        operations=10,multiplications=6,additions_subtractions=4,equations=1,
        degree_upper_bound=7,required_power_interface='Q=8**(32*x), ordinary x>0',
        valid_program_recipe='program_A=(8**64-1)*8**17*enc8(S)+h6; S is the exact primary program word')


def execute(source,values):
    env=dict(values)
    for n,op,a,b in source:
        x=env[a] if isinstance(a,str) else a;y=env[b] if isinstance(b,str) else b
        env[n]=x*y if op=='*' else x+y if op=='+' else x-y
    return env


def polynomial_source(packet):
    return packet['source']+[('query_output','-','query_numerator','query_scaled_word')],'query_output'


def verify():
    packet=build();source,out=polynomial_source(packet);counts=Counter(op for _,op,_,_ in packet['source'])
    assert counts=={'*':6,'-':4}
    degrees={n:1 for n in packet['parameters']}
    for n,op,a,b in source:
        da=degrees[a] if isinstance(a,str) else 0;db=degrees[b] if isinstance(b,str) else 0
        degrees[n]=da+db if op=='*' else max(da,db)
    assert degrees[out]==7
    examples=[];words=malformed=0
    for rank in (2,3,5):
      for relators in ((),((1,1),),((1,2,-1,-2),)):
        S=program_word(rank,relators);A=program_parameter(S);codes=code_for_group(rank)
        assert codes['alpha']==1 and codes['beta']==0 and len(set(codes.values()))==len(codes)
        special=[tuple(r) for r in relators]+[(i,-i) for i in range(1,rank+1)]+[(-i,i) for i in range(1,rank+1)]
        decoded=primary.decode_phi(S.translate(str.maketrans('cd','ab')),codes)
        expected=('alpha','alpha')
        for r in special:expected+=r+('alpha',)
        assert decoded==expected
        for x in range(1,25):
            word=query_word(S,x);Q=BASE**(32*x);W=encode(word)
            tail=word[len(S):]
            assert len(tail)==192*x+17
            assert primary.decode_phi(tail,codes)==('beta',)+primary.commutator_input(x)+('beta',)
            env=execute(source,dict(program_A=A,Q=Q,word=W));assert env[out]==0
            for delta in (-1,1):
                assert execute(source,dict(program_A=A,Q=Q,word=W+delta))[out]==-DENOMINATOR*delta
                malformed+=1
            words+=1
            if rank==2 and not relators and x<=2:
                examples.append(dict(x=x,program_length=len(S),query_length=len(word),
                    Q_bits=Q.bit_length(),word_bits=W.bit_length(),program_parameter_bits=A.bit_length()))
    rng=random.Random(321713);formal=0
    for _ in range(128):
        A,Q,W=(rng.randrange(-20,21) for _ in range(3))
        e=execute(source,dict(program_A=A,Q=Q,word=W))
        expected=A*Q**6+sum(COEFFICIENTS[i]*Q**i for i in (0,1,3,4))-DENOMINATOR*W
        assert e[out]==expected;formal+=1
    return dict(status='PASS_TSEYTIN_AFFINE_POWER_QUERY_LOADER',packet=packet,
        polynomial_operations=len(source),polynomial_source=source,output=out,
        source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest(),
        constants=dict(B=B,denominator=DENOMINATOR,tail_coefficients=COEFFICIENTS,leading_scale=LEADING_SCALE),
        checks=dict(literal_primary_query_codes=words,perturbed_word_residuals=malformed,formal_signed_Horner_outputs=formal),
        examples=examples,
        scope='Exact ten-gate input bridge on the explicitly required Q=8**(32*x) interface. No unpaid powers or divisions in the source, but this module alone does not certify Q or assert a universal operation bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['checks']);print(result['packet']['operations'])
