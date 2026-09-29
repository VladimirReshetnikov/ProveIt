"""A positive six-operation Collatz step and a scoped odd-loader obstruction."""
from pathlib import Path
import json
import sympy as sp

def certificate():
    A,beta,n,m=sp.symbols('A beta n m',integer=True,positive=True)
    env=dict(A=A,beta=beta,n=n,m=m)
    ops=[('twice_A','+','A','A'),('input_lhs','+','n',3),
        ('input_rhs','+','twice_A','beta'),('output_product','*','twice_A','beta'),
        ('output_lhs','+','m',1),('output_rhs','-','output_product','A')]
    histogram={'+':0,'*':0}
    for name,op,left,right in ops:
        l=env[left] if isinstance(left,str) else left;r=env[right] if isinstance(right,str) else right
        env[name]=l+r if op=='+' else l-r if op=='-' else l*r
        histogram['*' if op=='*' else '+']+=1
    source=[n+3-2*A-beta,m+1-2*A*beta+A]
    pairs=[('input_lhs','input_rhs'),('output_lhs','output_rhs')]
    assert all(sp.expand(env[l]-env[r]-p)==0 for (l,r),p in zip(pairs,source))
    assert histogram=={'+':5,'*':1}
    cases=0
    for value in range(1,2049):
        quotient=value//2+1;selector=value%2+1
        successor=value//2 if value%2==0 else (3*value+1)//2
        assert quotient>0 and selector in (1,2) and successor>0
        assert value+3==2*quotient+selector
        assert successor+1==2*quotient*selector-quotient
        assert selector*(3-selector)==2;cases+=1
    return dict(operations=6,histogram=histogram,positive_auxiliaries=['A','beta'],
        required_selector='beta in {1,2}',primitive_instructions=ops,
        source_equations=[sp.sstr(p) for p in source],direct_steps=cases,
        standalone_selector_extra_operations=2,standalone_total=8,
        scope='One scalar step. The native selector may come from a surrounding mask; otherwise beta*(3-beta)=2 costs two more operations. No parallel-history or universal-machine claim.')

def step(n,a,b):return n//2 if n%2==0 else (a*n+b)//2

def confirmed_trace(n,a,b,target,limit=160):
    seen=set();trace=[]
    for _ in range(limit+1):
        trace.append(n)
        if n==target:return trace
        if n in seen:return None
        seen.add(n);n=step(n,a,b)
    return None

def order_two(a):
    if a==1:return 1
    value=2%a;order=1
    while value!=1:value=2*value%a;order+=1
    assert order<a
    return order

def inverse_family():
    confirmed=families=unclassified=0
    for a in range(1,10,2):
        L=order_two(a)
        for b in range(1,10,2):
            for target in range(1,17):
                for n in range(1,66,2):
                    trace=confirmed_trace(n,a,b,target)
                    if trace is None:unclassified+=1;continue
                    if n==target:continue
                    assert len(trace)>1 and trace[0]==n
                    y=trace[1];assert y==(a*n+b)//2 and y>0
                    previous=n;confirmed+=1
                    for k in range(1,4):
                        numerator=2**(1+k*L)*y-b
                        alias,rem=divmod(numerator,a)
                        assert rem==0 and alias%2==1 and alias>previous
                        v=step(alias,a,b);assert v==2**(k*L)*y
                        for _ in range(k*L):assert v%2==0;v//=2
                        assert v==y and trace[-1]==target
                        previous=alias;families+=1
    # Sharp exceptional singleton for the positive raw loader n=2x+1.
    for x in range(1,513):
        n=2*x+1
        if n==5:assert x==2
        else:assert step(n,3,3)%3==0
    return dict(confirmed_nontrivial_odd_seeds=confirmed,constructed_odd_predecessors=families,
        cutoff_or_cycle_cases_not_used_as_halting_evidence=unclassified,
        singleton_example=dict(a=3,b=3,target=5,raw_loader='2x+1',accepted_positive_input=2),
        scope='Each predecessor follows an explicitly checked odd step and a finite halving chain into a confirmed target-reaching suffix. Finite cutoffs do not classify an orbit. The unbounded theorem is in the proof.')

def verify():
    return dict(status='PASS_TWO_BRANCH_COLLATZ_SCALAR_AND_LOADER_BOUNDARY',
        scalar=certificate(),inverse_family=inverse_family(),
        proof='../1980/EXPLORATION_TWO_BRANCH_COLLATZ_PRIMITIVE.md',
        scope='A cheaper exact scalar primitive and an obstruction for direct/odd affine raw loaders, not a complete history certificate or a new universal bound.')

if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status']);print(result['scalar']);print(result['inverse_family'])
