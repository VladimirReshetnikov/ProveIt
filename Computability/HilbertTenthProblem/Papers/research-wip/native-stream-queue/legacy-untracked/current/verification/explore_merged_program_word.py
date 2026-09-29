"""Exact bounded tests and a modular obstruction for merged program words."""
from pathlib import Path
import json
from math import gcd
import explore_interleaved_grid_complements as baseline

def bits(n):
    result=set();i=0
    while n:
        n,d=divmod(n,3);assert d<2
        if d:result.add(i)
        i+=1
    return result

def subset_sums(values):
    out=[0]
    for v in values:out.extend([x+v for x in out])
    return out

def check(a,edges,u):
    d=4*max(a);m=2*(d+3*max(a));R=3**m;q=R**u;I=3**a[0];g=3**d
    positions=[d+a[j]-a[i] for i,j in edges]+[d-x for x in a]
    assert len(set(positions))==len(positions)
    K=sum(3**p for p in positions);S=sum(3**p for p in a)
    floor=d+min(a)-max(a);correct=set()
    for i,j in edges:
        correct |= bits((K+1)*3**a[i]-g*3**a[j])
    assert correct<=set(a)|set(range(floor,m))
    weights=[3**(row*m+p) for row in range(u) for p in sorted(correct)]
    assert len(weights)<=40
    A=R//g*(K+1)-1;target=(-(K+1)*I*(q-1))%A
    cut=len(weights)//2;left=subset_sums(weights[:cut]);right=subset_sums(weights[cut:])
    by_mod={}
    for f in left:by_mod.setdefault(f%A,[]).append(f)
    solutions=[]
    for fr in right:
        for fl in by_mod.get((target-fr)%A,[]):
            F=fl+fr;num=g*I*(q-1)+R*F;den=R*(K+1)-g
            C,rem=divmod(num,den);assert rem==0
            if not 0<C<F<q:continue
            assert (R*K-g)*C==g*I*(q-1)+R*(F-C)
            cbits=bits(C) if all(int(d)<2 for d in ternary(C)) else None
            allowed={row*m+p for row in range(u) for p in a}
            solutions.append(dict(C=str(C),F=str(F),initial_correct=C%R==I,
                state_supported=cbits is not None and cbits<=allowed))
    return dict(a=a,edges=edges,height=u,width=m,allowed_row_positions=sorted(correct),
        Boolean_fields=len(weights),total_words=2**len(weights),meet_in_middle_sums=len(left)+len(right),
        complete_solutions=len(solutions),bad_initial=sum(not x['initial_correct'] for x in solutions),
        bad_state_support=sum(not x['state_supported'] for x in solutions),solutions=solutions)

def ternary(n):
    out=[]
    while n:n,d=divmod(n,3);out.append(d)
    return out

def modular_repetition():
    cases=0
    for modulus in range(2,81):
        for base in range(2,17):
            if gcd(base,modulus)!=1:continue
            order=1;value=base%modulus
            while value!=1:value=value*base%modulus;order+=1
            assert order<modulus
            count=2*modulus*order
            power=1;total=0
            for _ in range(count):total=(total+power)%modulus;power=power*base%modulus
            assert total==0 and power==1;cases+=1
    return dict(coprime_base_modulus_cases=cases,
        repetition_choice='2*d*ord_d(R^6)',
        scope='Checks the general geometric-repetition congruence at finite moduli. The actual large modulus uses the proved order argument, not a materialized repeated word.')

def false_program_family():
    c=baseline.PROGRAM;ell=baseline.ELL;a=c['a']
    positions=bits(c['K'])
    shift=max(0,max(a)+ell-min(positions));shift+=(-shift)%ell
    scale=3**shift;K=c['K']*scale;g=c['g']*scale
    hs=c['hs']*scale;hz=c['hz']*scale;I=c['I']
    copy_boundary=min(bits(K));assert copy_boundary>max(a)
    rows={};Ubits=set()
    for i,j in c['edges']:
        sign=int(c['signs'][i]>0);nozero=1-c['zeros'][i]
        state=3**a[i]
        f=(K+1)*state-g*3**a[j]-hs*sign-hz*nozero
        fb=bits(f);assert f>state and f%3**copy_boundary==state
        rows[i,j]=f;Ubits|=fb
    U=sum(3**b for b in Ubits)
    m=max(Ubits)+ell;m+=(-m)%ell;R=3**m
    while R<=max(2*U,(K+g)*(c['S']+1),g*(I+1)):
        m+=ell;R*=3**ell
    assert R%g==0 and R*I>3**a[5]
    period=6;states=list(range(period));nexts=[1,2,3,4,5,3]
    Cseed=sum(3**a[i]*R**b for b,i in enumerate(states))
    Fseed=sum(rows[i,j]*R**b for b,(i,j) in enumerate(zip(states,nexts)))
    kp=sum(R**b for b,i in enumerate(states) if c['signs'][i]>0)
    km=sum(R**b for b,i in enumerate(states) if c['signs'][i]<0)
    z=sum(c['zeros'][i]*R**b for b,i in enumerate(states))
    nz=sum((1-c['zeros'][i])*R**b for b,i in enumerate(states))
    heads=sum(R**b for b in range(period));Oseed=hs*kp+hz*nz
    assert min(kp,km,z,nz)>0 and kp+km==z+nz==heads
    assert Fseed>Cseed>0 and 3**a[3]>I
    assert U*heads-Fseed>0
    T=R//g;den=(K+1)*T-1
    assert gcd(den,R)==1 and den>1
    defect=R**period*(3**a[3]-I)
    numerator=T*(Fseed+Oseed)+I*(R**period-1)
    assert numerator==den*Cseed-defect
    assert 0<numerator<den*Cseed<den*Fseed
    assert (R*K-g)*Cseed-g*I*(R**period-1)-R*(Fseed-Cseed+Oseed)==g*defect
    assert all(i in Ubits for i in a)
    return dict(fixed_states=len(a),fixed_legal_edges=len(c['edges']),
        added_g_exponent=shift,copy_boundary=copy_boundary,counter_width=m,
        fixed_union_positions=len(Ubits),period=period,states=states,virtual_successors=nexts,
        true_zero_labels=[c['zeros'][i] for i in states],
        all_four_flags_positive=True,route_seed_identity=True,positive_C_and_V_numerators=True,
        first_six_rows_unchanged=True,
        construction='For G divisible by den, C=numerator*(G/den), V=Fseed*G-C; q=R^(6k), G=(q-1)/(R^6-1).',
        scope='Constructive infinite program-level counterfamily, with exact fixed-row support, positive C/V and all four typed flags. The geometric repetition is not materialized. The complete raw-counter time equation is not claimed.')

def verify():
    out=[]
    for a,e,u,want in [([4,12],[(0,1),(1,0)],2,1),([4,12],[(0,1),(1,0)],4,1),([4,12,36],[(0,1),(1,2),(2,0)],2,0)]:
        r=check(a,e,u)
        assert r['complete_solutions']==want
        assert r['bad_initial']==r['bad_state_support']==0
        out.append(r)
    return dict(status='PASS_MERGED_PROGRAM_WORD_PROGRAM_TYPING_REFUTED',
        cases=out,total_Boolean_words=sum(r['total_words'] for r in out),
        meet_in_middle_sums=sum(r['meet_in_middle_sums'] for r in out),
        repetition=modular_repetition(),counterfamily=false_program_family(),
        proof='../1980/EXPLORATION_MERGED_PROGRAM_WORD.md',
        scope='The merged program masks and route do not imply separate state/junk typing: an infinite positive program-level counterfamily is proved. Small exhaustive checks remain as accurately scoped evidence. No full raw-counter counterexample or99-operation universal construction is claimed.')

if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'])
    for r in result['cases']:print({k:v for k,v in r.items() if k!='solutions'})
    print(result['repetition']);print(result['counterfamily'])
