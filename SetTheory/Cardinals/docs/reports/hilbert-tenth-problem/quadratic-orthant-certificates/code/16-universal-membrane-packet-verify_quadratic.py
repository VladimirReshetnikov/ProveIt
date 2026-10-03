#!/usr/bin/env python3
"""Check the explicit degree-two schema without trusting its evaluator.
Small accepting toy-table fixtures exercise both counters and both SUB outcomes.
Actual full-table fixtures certify prefixes and reject the non-HALT terminal.
No huge accepting microtrace is generated.
"""
from pathlib import Path
import json,random
from collections import Counter
from fractions import Fraction
from quadratic_outcome import semantic_table,compile_schema,witness_for_trace
R=Path(__file__).resolve().parent
stats={'natural_domain_mutations_rejected':0,'witness_mutations_rejected':0}

def validate_and_eval(p,w,A):
    V=p['variables']['count'];forms=p['linear_forms']
    assert type(A) is int and A>=1
    assert all(type(i) is int and 0<=i<V and (type(v) is int or isinstance(v,Fraction)) and v>=0 for i,v in w.items())
    for name,terms in forms.items():
        assert len({i for i,c in terms})==len(terms)
        assert all(type(i) is int and 0<=i<V and type(c) is int and c!=0 for i,c in terms)
    formvals={name:sum(w.get(i,0)*c for i,c in terms) for name,terms in forms.items()}
    def av(a):
        assert set(a)=={'forms','variables','parameters','constant'} and type(a['constant']) is int
        assert all(name in formvals and type(c) is int for name,c in a['forms'])
        assert all(type(i) is int and 0<=i<V and type(c) is int for i,c in a['variables'])
        assert all(name=='raw_A' and type(c) is int for name,c in a['parameters'])
        return a['constant']+sum(c*formvals[f] for f,c in a['forms'])+sum(c*w.get(i,0) for i,c in a['variables'])+sum(c*A for name,c in a['parameters'])
    total=0;viol=[]
    for sq in p['affine_squares']:
        value=av(sq['affine']);total+=value*value
        if value:viol.append((sq['name'],value))
    for z in p['quadratic_products']:
        left=av(z['left']);right=av(z['right'])
        assert min(left,right)>=0
        total+=left*right
        if left*right:viol.append((z['name'],left*right))
    assert len(p['affine_squares'])==p['ledger']['affine_squares']
    assert len(p['quadratic_products'])==p['ledger']['quadratic_products']
    return total,viol

def literal_run(prog,T,A):
    q=prog['entry'];a=A;b=0;trace=[]
    for j in range(T):
        assert q!='HALT'
        trace.append((q,a,b));op,i,*dst=prog['rows'][q];regs=[a,b]
        if op=='ADD':regs[i]+=1;q=dst[0]
        elif regs[i]:regs[i]-=1;q=dst[0]
        else:q=dst[1]
        a,b=regs
    return q,a,b,trace

def expand_small(packet):
    # Parameter raw_A has token -1; all witness tokens are their nonnegative IDs.
    def linear(a):
        out=Counter({():a['constant']})
        for f,c in a['forms']:
            for i,k in packet['linear_forms'][f]:out[(i,)]+=c*k
        for i,c in a['variables']:out[(i,)]+=c
        for name,c in a['parameters']:
            assert name=='raw_A';out[(-1,)]+=c
        return {m:c for m,c in out.items() if c}
    def multiply(a,b):
        out=Counter()
        for m,c in a.items():
            for n,d in b.items():out[tuple(sorted(m+n))]+=c*d
        return out
    out=Counter()
    for row in packet['affine_squares']:
        a=linear(row['affine']);out.update(multiply(a,a))
    for term in packet['quadratic_products']:
        out.update(multiply(linear(term['left']),linear(term['right'])))
    return {m:c for m,c in out.items() if c}

def eval_expanded(poly,w,A):
    total=0
    for monomial,c in poly.items():
        term=c
        for i in monomial:term*=A if i==-1 else w.get(i,0)
        total+=term
    return total

program=json.loads((R/'literal2.json').read_text());table=semantic_table(program)
assert json.loads((R/'semantic_branches.json').read_text())==table
B=len(table['branches']);S=table['sub_count']
assert (B,S,3*B-S)==(10748,2340,29904)
# Independently compare both arms to every source instruction.
cur=0
for source,(name,row) in enumerate(program['rows'].items()):
    op,r,*dst=row;count=1 if op=='ADD' else 2
    bb=table['branches'][cur:cur+count];cur+=count
    assert all(z['source']==source and z['register']==r for z in bb)
    assert [table['labels'][z['target']] for z in bb]==dst
    assert [z['guard'] for z in bb]==([None] if op=='ADD' else ['positive','zero'])
    expect=[int(r==0),int(r==1)]
    assert bb[0]['delta']==(expect if op=='ADD' else [-x for x in expect])
    if op=='SUB':assert bb[1]['delta']==[0,0]
assert cur==B
stats['semantic_branches_checked']=B
stored=json.loads((R/'quadratic_schema_T1.json').read_text())
assert stored==compile_schema(table,1)
assert stored['ledger']=={'natural_witnesses':29904,'affine_squares':5,'quadratic_products':10748,'degree_at_most':2}
for T in (1,2):
    p=stored if T==1 else compile_schema(table,T)
    for A in (1,2,7,64):
        w,last,counters,trace=witness_for_trace(table,T,A)
        label,a,b,literaltrace=literal_run(program,T,A)
        assert (table['labels'][last],*counters)==(label,a,b)
        assert [(table['labels'][z['source']],*z['registers']) for z in trace]==literaltrace
        total,viol=validate_and_eval(p,w,A)
        assert total==(last-table['halt'])**2 and viol==[('terminal',last-table['halt'])]
        # A prefix fixture changes only the explicit requested terminal code.
        prefix=compile_schema(table,T,target=last)
        assert validate_and_eval(prefix,w,A)==(0,[])
        stats['actual_table_prefix_cases']=stats.get('actual_table_prefix_cases',0)+1
# Strengthened gates reject fractional one-hot relaxations even with every base zero.
for first,second in ((0,1),(0,B-1),(B//2,B-1)):
    fractional={first:Fraction(1,2),second:Fraction(1,2)}
    val,viol=validate_and_eval(stored,fractional,1)
    gates=[x for name,x in viol if name.startswith('inactive:')]
    assert gates==[Fraction(1,4),Fraction(1,4)] and val>=Fraction(1,2)
    stats['fractional_selector_gates_checked']=stats.get('fractional_selector_gates_checked',0)+1
p0=compile_schema(table,0)
assert validate_and_eval(p0,{},1)[0]>0
stats['zero_time_rejected']=True
# Valid small accepting fixtures exercise positive/zero outcomes for both counters.
toys=[
 {'entry':'s','rows':{'s':['SUB',0,'n','HALT'],'n':['SUB',0,'HALT','HALT']}},
 {'entry':'s','rows':{'s':['ADD',1,'n'],'n':['SUB',1,'HALT','HALT']}},
 {'entry':'s','rows':{'s':['SUB',1,'n','HALT'],'n':['ADD',0,'s']}}
]
fixtures=[]
for number,prog in enumerate(toys):
    tab=semantic_table(prog);T=1 if number==2 else 2;p=compile_schema(tab,T)
    expanded=expand_small(p);assert max(map(len,expanded))<=2
    stats['expanded_toy_polynomials']=stats.get('expanded_toy_polynomials',0)+1
    for A in range(1,17):
        w,last,cs,tr=witness_for_trace(tab,T,A)
        assert last==tab['halt'] and validate_and_eval(p,w,A)==(0,[])
        assert literal_run(prog,T,A)[0]=='HALT'
        stats['accepting_toy_cases']=stats.get('accepting_toy_cases',0)+1
        # Every coordinate occurs in the ledger, including its omitted zero values.
        for i in range(p['variables']['count']):
            mutant=dict(w);mutant[i]=mutant.get(i,0)+1
            assert validate_and_eval(p,mutant,A)[0]>0
            stats['witness_mutations_rejected']+=1
        if A==1:
            fixtures.append({'program':prog,'schema':p,'raw_A':A,'sparse_natural_witness':[[i,v] for i,v in sorted(w.items())],'expanded_polynomial':[[list(m),c] for m,c in sorted(expanded.items())],'parameter_token':-1})
        # Nonnegative selectors off the one-hot locus cannot make a negative summand.
        rng=random.Random(17+number+A)
        for k in range(5):
            mutant={i:rng.randrange(4) for i in range(p['variables']['count'])}
            value,_=validate_and_eval(p,mutant,A)
            assert eval_expanded(expanded,mutant,A)==value
            stats['off_constraint_nonnegative_checks']=stats.get('off_constraint_nonnegative_checks',0)+1
# API evaluator checks invalid-domain data too.
from quadratic_outcome import evaluate
for bad in ({-1:1},{29904:1},{0:-1},{0:1.5},{0:True}):
    try:evaluate(stored,bad,1)
    except ValueError:stats['natural_domain_mutations_rejected']+=1
    else:raise AssertionError(bad)
(R/'quadratic_small_fixtures.json').write_text(json.dumps(fixtures,indent=2)+'\n')
receipt={'status':'passed','checks':stats,'full_program_per_step':{'branches':B,'SUB_instructions':S,'natural_witnesses':3*B-S,'affine_squares_except_terminal':4,'nonnegative_products':B},
 'scope':'Exact fixed-T degree-two outcome family over natural witnesses. Small accepting fixtures and full-table prefix checks; no full universal accepting physical trace was materialized. PROOF.md gives all-input soundness/completeness and unique fibers.'}
(R/'quadratic_verification_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
