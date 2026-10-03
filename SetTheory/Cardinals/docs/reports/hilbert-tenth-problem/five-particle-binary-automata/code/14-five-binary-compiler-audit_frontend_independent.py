"""Exact independent SOS audit, including rational nonnegative selectors."""
import hashlib,itertools,json
from fractions import Fraction
from pathlib import Path
from five_binary import Machine,BinaryCA
from frontend import Frontend
ROOT=Path(__file__).parent
counts={}
def add(k,n=1):counts[k]=counts.get(k,0)+n

def candidate(f,choices):
    out=[0]*len(f.names);a,b=f.initial_counters;time=0
    for t,j in enumerate(choices):
        branch=f.branches[j]
        out[f.selectors[t][j]]=1
        if branch.op in ('ZERO','NOP'):time+=1
        else:
            c=(a,b)[branch.counter]
            time+=3+2*(f.ca.Z+c)+branch.delta-2*f.ca.K-2*f.ca.C-f.ca.codes['O',branch.source]-f.ca.codes['I',branch.source]
        if branch.counter==0:a+=branch.delta
        elif branch.counter==1:b+=branch.delta
        if min(a,b)<0:return None
        out[f.counter_variables[t][0]]=a;out[f.counter_variables[t][1]]=b
    if f.clock:out[f.theta]=time
    return out

def compositions(n,k):
    if k==1:yield (n,);return
    for x in range(n+1):
        for rest in compositions(n-x,k-1):yield (x,)+rest

def run():
    machines=[Machine({},'H','H'),Machine({'a':['NOP','H']},'a','H'),
        Machine({'a':['SUB',0,'H','b'],'b':['SUB',1,'a','H']},'a','H'),
        Machine({'a':['ADD',0,'b'],'b':['SUB',1,'a','c'],'c':['NOP','H']},'a','H'),
        Machine({'a':['ADD',0,'H'],'b':['ADD',0,'b'],'c':['ADD',0,'H']},'b','H')]
    for m in machines:
        ca=BinaryCA(m)
        for q in ca.states:
            for a,b in itertools.product(range(3),repeat=2):
                for h in range(4):
                    for real,clock in itertools.product((False,True),repeat=2):
                        f=Frontend(ca,h,q,(a,b),clock,real)
                        expected=f.witness();zeros=[]
                        for choices in itertools.product(range(f.B),repeat=h):
                            w=candidate(f,choices)
                            if w is not None and f.evaluate(w)==0:zeros.append(w)
                            add('onehot_branch_sequences')
                        assert zeros==([] if expected is None else [expected]),(m.rows,q,a,b,h,real,clock)
                        z=sum(x.op=='ZERO' for x in f.branches)
                        assert len(f.names)==h*(f.B+2)+clock
                        assert len(f.residuals)==(h*(4+z+real)+1+clock if h else 1+clock)
                        assert all(len(mon)<=2 for _,terms in f.residuals for _,mon in terms)
                        ledger=f.ledger();lengths=[len(terms) for _,terms in f.residuals]
                        assert ledger['residual_monomial_occurrences']==sum(lengths)
                        assert ledger['expanded_square_ordered_term_occurrence_bound']==sum(x*x for x in lengths)
                        if h and not clock:
                            assert sum(lengths)<=h*(4*f.B+5)+2+real*h*(f.B+1)
                        if expected is not None and real:
                            for k in range(len(expected)):
                                w=[Fraction(x) for x in expected];w[k]+=Fraction(1,2)
                                assert f.evaluate(w)>0
                                add('rational_coordinate_mutations')
                        add('fixed_input_frontends')
    # Unpaid real relaxation can invent a halted branch mixture at a looping
    # control; paid selector norm excludes this exact rational witness.
    ca=BinaryCA(machines[-1])
    unpaid=Frontend(ca,1,'b',(0,0),clock=True)
    paid=Frontend(ca,1,'b',(0,0),clock=True,nonnegative_real=True)
    w=[Fraction(0)]*len(paid.names)
    for t in ('a','c'):
        j=next(j for j,b in enumerate(paid.branches) if b.source==t)
        w[paid.selectors[0][j]]=Fraction(1,2)
    w[paid.counter_variables[0][0]]=1
    w[paid.theta]=sum(Fraction(ca.duration(q,0,0),2) for q in ('a','c'))
    # Use a direct rational evaluator for the natural-domain polynomial, rather
    # than bypassing or changing the runtime's natural-domain rejection.
    def exact_residuals(f,w):
        out={}
        for name,terms in f.residuals:
            acc=Fraction(0)
            for coef,mon in terms:
                value=Fraction(coef)
                for i in mon:value*=w[i]
                acc+=value
            out[name]=acc
        return out
    assert unpaid.witness() is None and paid.witness() is None
    assert all(x==0 for x in exact_residuals(unpaid,w).values())
    assert exact_residuals(paid,w)['0.selector_norm']==Fraction(-1,2)
    assert paid.evaluate(w)==Fraction(1,4)
    add('spurious_unpaid_fractional_witness_excluded')
    for B in range(1,7):
        for denom in range(1,9):
            for nums in compositions(denom,B):
                e=[Fraction(n,denom) for n in nums]
                assert sum(e)==1
                norm=sum(x*x for x in e)
                assert (norm==1)==(sum(n>0 for n in nums)==1)
                add('rational_simplex_points')
    report={'status':'passed','frontend_sha256':hashlib.sha256((ROOT/'frontend.py').read_bytes()).hexdigest(),
        'counts':counts,'paid_real_scope':'Nonnegative-real witnesses with fixed natural input counters, fixed control, and syntactically fixed horizon. No strict-interior or unbounded-horizon claim.',
        'proof':'sum e=1 and e>=0 imply 0<=e<=1; sum e^2=1 then sum e(1-e)=0 forces each e in {0,1}. Deterministic recurrence forces integer counter and clock coordinates.',
        'h0_clock_note':'The emitted unsimplified h=0 clock version has one Theta witness constrained to zero and two residual slots.'}
    (ROOT/'audit_frontend_independent.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':run()
