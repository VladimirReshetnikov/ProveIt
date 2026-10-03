import json,itertools,random
from pathlib import Path
import scheduler_reference as s
import example_emitter as e
HERE=Path(__file__).resolve().parent

def check(value,detail):
    if not value:raise RuntimeError(detail)

def source():
    return dict(schema='reversible-two-counter-v1',controls=['q','halt'],start='q',halt='halt',class_cut=0,
       branches=[dict(name='e',source='q',target='halt',side=1,delta=1,guard=dict(op='true'))])

def eval_serialized(rows,values):
    score=0
    for row in rows:
        total=0
        for coefficient,monomial in row:
            term=coefficient
            for index in monomial:term*=values[index]
            total+=term
        score+=total*total
    return score

def main():
    a=s.lazy.compile_lazy_source(source());eager=s.lazy.ref.compile_source(source())
    rng=random.Random(20261003);cases=[frozenset(),frozenset({-10**100}),frozenset({-118,-112,0,18,23})]
    for n in range(5):
        cases.extend(frozenset(v) for v in itertools.combinations(range(-3,5),n))
    for _ in range(80):
        gate=a.gate_at(rng.randrange(a.factors));x=set(rng.choice(gate.shapes));shift=rng.randrange(-100,100)
        x={v+shift for v in x}
        if rng.randrange(3)==0:x|={v+10000 for v in x}
        for j in range(rng.randrange(3)):x.add(rng.randrange(-100,100))
        cases.append(frozenset(x))
    total_events=0;absence=0;candidate_equal=0;underbudget=0
    for x in cases:
        actual_candidates=set(a.candidate_indices(x))
        generated={i for enabled,i in s.slots(a,x) if enabled}
        check(generated==actual_candidates,('candidate mismatch',x,generated,actual_candidates));candidate_equal+=1
        y,stats=a.step(x,trace=True)
        check(y==eager.step(x),('eager mismatch',x))
        k=stats['changed_factors'];total_events+=k
        for budget in (k,k+2):
            ok,z,records=s.run(a,x,1,budget)
            check(ok and z==y,('scheduler mismatch',x,budget))
            check(sum(r['kind']=='change' for r in records)==k,'event count')
            check(sum(r['kind']=='complete' for r in records)==1,'absence count')
            check(all(r['kind']=='idle' for r in records[k+1:]),'noncanonical padding')
            absence+=1
        if k:
            ok,z,records=s.run(a,x,1,k-1);check(not ok,'underbudget accepted');underbudget+=1
    # Multiple steps spend a single global changing-factor budget.
    x=frozenset({-118,-112,0,18,23});y=x;k=0
    for _ in range(3):y,st=a.step(y,trace=True);k+=st['changed_factors']
    multistep_events=k
    ok,z,records=s.run(a,x,3,k);check(ok and z==y,'T=3 total-budget mismatch')
    check(sum(r['kind']=='complete' for r in records)==3,'T completion count')
    poly_cases=0
    for h in (-10**100,-10,0,10):
        for gap in range(1,15):
            for T in (0,1,2):
                x=frozenset({h,h+gap});y=x;k=0
                for _ in range(T):y,st=a.step(y,trace=True);k+=st['changed_factors']
                c,rounds,out=e.build(h,gap,T,k,target=sorted(y));check(c.score()==0,'polynomial zero')
                check(out==sorted(y),'polynomial CA mismatch');poly_cases+=1
                if k:
                    c,rounds,out=e.build(h,gap,T,k-1,target=sorted(y));check(c.score()>0,'polynomial underbudget')
    e.main()
    artifact=json.loads((HERE/'example-polynomial.json').read_text());witness=json.loads((HERE/'example-witness.json').read_text())
    vals=artifact['input_values']+witness
    check(eval_serialized(artifact['residuals'],vals)==0,'serialized zero')
    expanded={(tuple(m)):c for c,m in artifact['expanded_quartic']}
    check(e.evaluate(expanded,vals)==0,'expanded zero')
    mutations=0
    for i in range(artifact['input_count'],len(vals)):
        changed=list(vals);changed[i]+=1
        check(eval_serialized(artifact['residuals'],changed)>0,('single witness mutation passed',i));mutations+=1
    # Comparison primitive: exhaust all signed differences and bounded natural b,d.
    comparator_fibers=0
    for L in range(-8,9):
        solutions=[(b,d) for b in range(4) for d in range(12) if b*(b-1)==0 and L-(2*b-1)*d-b+1==0]
        check(solutions==[(1,L)] if L>=0 else solutions==[(0,-L-1)],('comparator fiber',L,solutions));comparator_fibers+=1
    receipt=dict(status='passed',optimized=not __debug__,candidate_set_matches=candidate_equal,
        eager_and_lazy_cases=len(cases),event_count=total_events,absence_and_padding_runs=absence,
        rejected_underbudget_runs=underbudget,multistep_events=multistep_events,polynomial_CA_cases=poly_cases,
        changed_witness_rejections=mutations,exhaustive_comparator_fibers=comparator_fibers,
        sample_ledger=artifact['ledger'],sample_expanded_monomials=len(expanded))
    filename='test-optimized-receipt.json' if not __debug__ else 'test-receipt.json'
    (HERE/filename).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
