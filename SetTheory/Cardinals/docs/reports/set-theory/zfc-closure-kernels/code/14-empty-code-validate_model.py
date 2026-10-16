"""Reproduce algebraic rejection of the fixed-slot 248/250 experiments."""
from pathlib import Path
import sys, json, itertools, collections, random, argparse
from base3_model import *
import formula_patterns as p

def main(output=None):
    result={}
    for n in range(100000):
        assert pair(*unpair(n))==n
        f=decode(n)
        assert encode(f)==n
        assert normalize(f)==f
        assert all(i<n for i in labels(f))
    result['natural_code_roundtrips_and_freshness']=100000
    for truth,star in ((value,False),(value_star,True)):
        for a in range(150):
            for b in range(150):
                assert truth(imp(a,b)) == (not truth(a) or truth(b))
                atom_value=((a!=b) if star else (a==1)) and truth(b)
                assert truth(rel(a,b)) == atom_value
                assert truth(all_(a,b)) == truth(b)
    result['constructor_homomorphism_checks']=2*3*150*150
    assert value(0) and not value(1)
    count=0
    for kernel,swap,c,star in itertools.product(('subset','empty'),(False,True),range(4096),(False,True)):
        assert evaluate_pattern(p.psc(kernel,swap),{'c':c},star)
        count+=1
    result['fixed_slot_theory_pattern_checks']=count
    rng=random.Random(20261016)
    count=0
    for _ in range(10000):
        vals={s:rng.randrange(100000) for s in ('a','b','c','u','h')}
        for star,truth in ((False,value),(True,value_star)):
            for row in p.retained_logic():
                assert evaluate_pattern(row,vals,star);count+=1
            if truth(vals['h']): assert evaluate_pattern(p.All('a','h'),vals,star)
    result['logical_row_pattern_checks']=count
    count=0
    for a,b,c,kernel,swap in itertools.product(range(32),range(32),range(32),('subset','empty'),(False,True)):
        if c==a or c==b:continue
        assert evaluate_pattern(p.psc(kernel,swap,'a','b','c'),{'a':a,'b':b,'c':c},True)
        count+=1
    result['variable_parameter_wrapper_star_checks']=count
    for a in range(100000):assert not value_star(rel(a,a))
    result['irreflexivity_star_checks']=100000
    witness=imp(all_(2,rel(1,2)),rel(1,1))
    assert not value(witness) and not value_star(witness)
    result['pure_logic_missing_instantiation']={
        'formula':'All(2,Rel(1,2)) -> Rel(1,1)',
        'valuation':{'All':'identity','Rel(1,2)':True,'Rel(1,1)':False},
        'value':False,'first_order_valid':True}
    result['status']='All bounded checks pass. Universal claims proved separately in report.'
    result['interpretation']='Boolean formula algebra, not ordinary membership semantics'
    count=0
    for size in (1,2,3):
        domain=range(size)
        possible_edges=[(x,y) for x in domain for y in domain if x!=y]
        for mask in range(1<<len(possible_edges)):
            edges={edge for i,edge in enumerate(possible_edges) if mask>>i&1}
            member=lambda x,y:(x,y) in edges
            for kernel,swap,c in itertools.product(('subset','empty'),(False,True),(0,1)):
                f=instantiate_pattern(p.psc(kernel,swap),{'c':c})
                for e0,e1 in itertools.product(domain,domain):
                    assert semantic_value(f,member,domain,{0:e0,1:e1}) == (bool(edges) if c==0 else True)
                    count+=1
    result['ordinary_irreflexive_low_code_cases']=count
    if output is not None:
        Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    main(parser.parse_args().output)
