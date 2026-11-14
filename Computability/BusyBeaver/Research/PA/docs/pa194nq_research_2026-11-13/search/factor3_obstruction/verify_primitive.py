#!/usr/bin/env python3
"""Independent primitive-rule verifier for the factor-three refutation.

No K/S rule, Lean parser, propositional tautology test, model assumption,
or machine simulator is used. Terms are exact arithmetic expression DAGs.
I means 3*Cantor(left,right), U means 3*Cantor(body,binder)+2.
"""
from pathlib import Path
import json,hashlib,collections,functools,time
if not __debug__:
    raise RuntimeError('Run with assertions enabled; do not use Python -O.')
HERE=Path(__file__).resolve().parent

def verify(path):
    started=time.monotonic()
    data=json.loads(path.read_text())
    assert data['format']=='numeric-term-dag-v1'
    terms=data['terms'];proofs=data['proofs']
    assert terms[:2]==[['nat',0],['nat',1]]
    by_term={('nat',0):0,('nat',1):1}
    depths=[0,0]
    for index,node in enumerate(terms[2:],2):
        assert len(node)==3 and node[0]in('I','U')
        _,a,b=node
        assert type(a)is int and type(b)is int and 0<=a<index and 0<=b<index
        assert node!=['I',0,0], 'I(0,0) must use canonical literal zero'
        assert tuple(node)not in by_term,'duplicate arithmetic term'
        by_term[tuple(node)]=index
        depths.append(1+max(depths[a],depths[b]))
    def I(a,b):
        return 0 if a==b==0 else by_term['I',a,b]
    def U(a,b):return by_term['U',a,b]
    def R(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
    @functools.lru_cache(None)
    def implication_component(small,large):
        # Every path is a chain of a<=I(a,b) or b<=I(a,b),
        # valid for the concrete Cantor arithmetic defining I.
        if small==large:return True
        node=terms[large]
        return node[0]=='I' and (implication_component(small,node[1])or
                                 implication_component(small,node[2]))
    conclusions=[];counts=collections.Counter()
    for index,line in enumerate(proofs):
        rule=line['rule'];args=line['args'];out=line['conclusion']
        assert type(out)is int and 0<=out<len(terms)
        def formula(proof_index):
            assert type(proof_index)is int and 0<=proof_index<index
            return conclusions[proof_index]
        def term_indices(values):
            assert all(type(i)is int and 0<=i<len(terms)for i in values)
        if rule=='rho8':
            assert len(args)==4;term_indices(args)
            a,b,c,u=args
            assert implication_component(u,a),('unverified numerical bound',index)
            assert out==R(a,b,c,u)
        elif rule=='mp':
            assert len(args)==2
            major,minor=args
            assert formula(major)==I(formula(minor),out),('invalid MP',index)
        elif rule=='gen':
            assert len(args)==2
            binder,source=args;term_indices([binder])
            assert out==U(binder,formula(source))
        elif rule=='head5_0_1':
            assert args==[]
            # Exact arithmetic identity E(1,0)=3*pair(1,0)+3
            # =6=3*pair(0,1)=I(0,1).
            pair=lambda a,b:(a+b)*(a+b+1)//2+b
            assert 3*pair(1,0)+3==3*pair(0,1)==6
            equality_1_0=I(0,1)
            assert out==I(U(0,I(equality_1_0,1)),1)
        else:raise AssertionError(('nonprimitive rule',rule))
        conclusions.append(out);counts[rule]+=1
    final=data['final']
    assert type(final)is int and 0<=final<len(proofs) and conclusions[final]==1
    return dict(status='PASS',arithmetic_terms=len(terms),maximum_term_depth=max(depths),
        primitive_proof_steps=len(proofs),rule_counts=dict(counts),final_conclusion=1,
        certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        seconds=time.monotonic()-started,
        assumptions='Only the four explicitly checked primitive rules and elementary Cantor-component bounds; no K/S oracle and no Lean compilation claim')

if __name__=='__main__':
    result=verify(HERE/'primitive_proof.json')
    (HERE/'primitive_result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
