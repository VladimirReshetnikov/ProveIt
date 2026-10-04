#!/usr/bin/env python3
"""Fresh audit tests: no import or execution of submitted/upstream code.
Only Python standard-library arithmetic. Source formulas transcribed manually.
Finite checks complement, and do not substitute for, the proofs in report.md.
"""
import itertools
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent
stats = {}

def pack(ds, base):
    return sum(d * base**i for i, d in enumerate(ds))

def recurrence_checks():
    cases = 0
    brute_candidates = 0
    for b in range(2, 7):
        for m in range(1, 4):
            Q = b**m
            for K in range(1, min(b, 5)):
                if m*K > 12:
                    continue
                W = Q**K
                inverse = pow(Q-1, -1, W)
                for bits in itertools.product((0, 1), repeat=m*K):
                    E = pack(bits, b)
                    counts = [0]*m
                    prior = []
                    for t in range(K):
                        prior.extend(counts)
                        counts = [counts[j] + bits[m*t+j] for j in range(m)]
                    expected_pre = pack(prior, b)
                    expected_final = pack(counts, b)
                    # Solve the complete integer recurrence over all candidate pre
                    # values in [0,W), rather than assuming candidate small digits.
                    candidate = (-Q*E*inverse) % W
                    numerator = (Q-1)*candidate + Q*E
                    assert numerator % W == 0
                    final = numerator//W
                    assert candidate == expected_pre
                    assert final == expected_final
                    assert Q*(candidate+E) == candidate+W*final
                    assert final < Q
                    if W <= 81:
                        for malicious_pre in range(W):
                            rhs = (Q-1)*malicious_pre+Q*E
                            brute_candidates += 1
                            if rhs % W == 0 and 0 <= rhs//W < Q:
                                assert malicious_pre == expected_pre
                    cases += 1
    stats['recurrence_event_streams'] = cases
    stats['recurrence_bruteforce_pre_candidates'] = brute_candidates


def geometric(base, n):
    return sum(base**i for i in range(n))

def literal_spread(value, base, length, stride):
    copybase = base**(stride-1)
    copy = geometric(copybase, length)
    mask = geometric(base**stride, length)
    return (value*copy) & ((base-1)*mask)

def spread_checks():
    cases=0
    for base in (2, 4, 8, 16, 32):
        for length in range(1, 6):
            for stride in range(length+1, length+4):
                limit=base**length
                samples=range(limit) if limit <= 4096 else sorted(set(
                    [0,1,limit-1,limit-2] + [random.Random(119+base+length).randrange(limit) for _ in range(1)] +
                    [((i*104729+17) % limit) for i in range(100)]))
                for value in samples:
                    digits=[(value//base**i)%base for i in range(length)]
                    assert literal_spread(value,base,length,stride) == sum(d*base**(stride*i) for i,d in enumerate(digits))
                    cases+=1
    stats['spread_macro_cases'] = cases


def spread_positions(poly, block, length, stride):
    assert all(0 <= i < block*length for i in poly)
    assert stride >= length+1
    return {(i%block)+block*stride*(i//block): c for i,c in poly.items()}

def repeat_positions(poly, offset, length):
    result={}
    for i,c in poly.items():
        for j in range(length):
            at=i+j*offset
            assert at not in result, ('unexpected copy collision', at)
            result[at]=c
    return result

def geometry_checks():
    rng=random.Random(77131)
    boxes=0
    slots=0
    for _ in range(80):
        p,q,r,d,e,f=[rng.randint(1,2) for _ in range(6)]
        tx=max(2,(q*r+1+2*d-1)//(2*d),(e*f+1+2*p-1)//(2*p))+rng.randint(0,2)
        ty=max(2,(r+1+2*e-1)//(2*e),(f+1+2*q-1)//(2*q))+rng.randint(0,2)
        tz=rng.randint(2,4)
        hx,hy,hz=p*d*tx,q*e*ty,r*f*tz
        A,B,C=2*hx,2*hy,2*hz
        N=A*B*C
        tile={i:rng.randrange(6) for i in range(p*q*r)}
        patch={i:rng.randrange(16) for i in range(d*e*f)}
        bg=spread_positions(tile,p,q*r,2*d*tx)
        bg=spread_positions(bg,A*q,r,2*e*ty)
        bg=repeat_positions(bg,p,2*d*tx)
        bg=repeat_positions(bg,A*q,2*e*ty)
        bg=repeat_positions(bg,A*B*r,2*f*tz)
        add=spread_positions(patch,d,e*f,2*p*tx)
        add=spread_positions(add,A*e,f,2*q*ty)
        shift=hx+A*hy+A*B*hz
        add={i+shift:c for i,c in add.items()}
        assert len(bg)==N
        for z in range(C):
            for y in range(B):
                for x in range(A):
                    j=x+A*y+A*B*z
                    physical=(x-hx,y-hy,z-hz)
                    ti=physical[0]%p+p*(physical[1]%q)+p*q*(physical[2]%r)
                    assert bg[j]==tile[ti]
                    ix,iy,iz=physical
                    expected=patch[ix+d*iy+d*e*iz] if (0<=ix<d and 0<=iy<e and 0<=iz<f) else 0
                    assert add.get(j,0)==expected
                    assert 0 <= bg[j]+add.get(j,0) <=20
        assert all(0<((i//(A*B))%C)<C-1 and 0<((i//A)%B)<B-1 and 0<(i%A)<A-1 for i in add)
        boxes+=1
        slots+=N
    stats['geometry_boxes']=boxes
    stats['geometry_slots']=slots


def mask_neighbor_target_checks():
    cases=0
    positions=0
    # Actual integer masks at a small power-of-two radix, rather than only
    # trusting the set description of the products.
    b=4
    for A,B,C in itertools.product(range(4,7),repeat=3):
        X,Y,Q=b**A,b**(A*B),b**(A*B*C)
        jx,jy,jz=geometric(b,A-2),geometric(X,B-2),geometric(Y,C-2)
        assert b*b*((b-1)*jx+1)==X
        assert X*X*((X-1)*jy+1)==Y
        assert Y*Y*((Y-1)*jz+1)==Q
        I=b*X*Y*jx*jy*jz
        expected={x+A*y+A*B*z for x in range(1,A-1) for y in range(1,B-1) for z in range(1,C-1)}
        assert I==sum(b**j for j in expected)
        for t in range(3):
            for z in range(1,C-1):
                for y in range(1,B-1):
                    for x in range(1,A-1):
                        j=x+A*y+A*B*z
                        for dx,dy,dz in ((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)):
                            shifted=j+t*A*B*C+dx+A*dy+A*B*dz
                            assert shifted//(A*B*C)==t
                            assert shifted%(A*B*C)==(x+dx)+A*(y+dy)+A*B*(z+dz)
                            positions+=1
        cases+=1
    stats['interior_integer_mask_cases']=cases
    stats['neighbor_shift_positions']=positions
    target_cases=0
    # Target bit membership is checked at every candidate time, including
    # late times, with even final counts explicitly present.
    A=B=C=4; N=A*B*C; Q=b**N; K=3
    j=1+A+A*B
    E=b**j+Q*b**j+Q**2*b**(j+1)
    for local in range(N):
        for tau in range(K+3):
            bit=b**local*Q**tau
            found=(E&bit)==bit
            assert found==((local,tau) in {(j,0),(j,1),(j+1,2)})
            target_cases+=1
    stats['target_bit_cases']=target_cases


def legality_checks():
    cases=0
    for K in range(1,101):
        b=32
        while b<64*(K+1): b*=32
        half=b//2
        assert 6*K+half-1 < b
        for t in range(K):
            # Endpoints and representative inner values; exhaustive for small K.
            own_values=range(t+1) if K<=8 else sorted({0,t//2,t})
            neighbor_values=range(6*t+1) if K<=8 else sorted({0,3*t,6*t})
            for own in own_values:
                for ns in neighbor_values:
                    for eta in range(21):
                        c=eta+ns
                        slack=c-6*own-6
                        assert c<b
                        assert (0<=slack<=half-1)==(c-6*own>=6)
                        if slack>=0:
                            assert c==6*own+6+slack<b
                        cases+=1
    stats['legality_local_cases']=cases

recurrence_checks()
spread_checks()
geometry_checks()
mask_neighbor_target_checks()
legality_checks()
report={'result':'All fresh finite checks passed','scope':'Fresh independent Python arithmetic only; submitted source and upstream programs were never imported or executed; Lean was not run. Finite tests are not a universal proof.','counts':stats}
(HERE/'independent-check-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))


def full_tableau_checks():
    b=1024; A=8; B=C=4; N=A*B*C
    X=b**A; Y=b**(A*B); Q=b**N
    origin=(4,2,2); target=(5,2,2)
    def index(v):return v[0]+A*v[1]+A*B*v[2]
    js=(index(origin),index(target))
    unit=(b**js[0],b**js[1])
    interior=sum(b**(x+A*y+A*B*z) for x in range(1,A-1) for y in range(1,B-1) for z in range(1,C-1))
    patterns=((0,0),(1,0),(0,1),(1,1))
    cases=valid=0
    for heights in ((12,4),(6,0),(5,5),(20,20)):
        eta=heights[0]*unit[0]+heights[1]*unit[1]
        for K in range(1,6):
            R=geometric(Q,K); W=Q**K
            for layers in itertools.product(patterns,repeat=K):
                counts=[0,0]; pre=E=0; is_legal=True; slack=0
                for t,events in enumerate(layers):
                    pre+=(counts[0]*unit[0]+counts[1]*unit[1])*Q**t
                    E+=(events[0]*unit[0]+events[1]*unit[1])*Q**t
                    for s in range(2):
                        if events[s]:
                            height=heights[s]+counts[1-s]-6*counts[s]
                            if height<6:is_legal=False
                            else:slack+=(height-6)*unit[s]*Q**t
                    counts=[counts[s]+events[s] for s in range(2)]
                final=counts[0]*unit[0]+counts[1]*unit[1]
                assert Q*(pre+E)==pre+W*final
                assert pre&((b-1)*interior*R)==pre
                assert E&(interior*R)==E
                assert final&((b-1)*interior)==final
                assert pre%b==pre%X==pre%Y==0
                available=eta*R+b*pre+X*pre+Y*pre+pre//b+pre//X+pre//Y
                selected=available&((b-1)*E)
                own=pre&((b-1)*E)
                # Natural lower-half slack exists iff digitwise subtraction
                # yields the direct physical legality verdict.
                candidate=selected-6*own-6*E
                satisfies=candidate>=0 and candidate&((b//2-1)*E)==candidate
                assert satisfies==is_legal
                if is_legal:
                    assert candidate==slack
                    valid+=1
                for s in range(2):
                    for t in range(K+1):
                        bit=unit[s]*Q**t
                        assert (E&bit==bit)==(t<K and layers[t][s]==1)
                cases+=1
    stats['full_enlarged_radix_tableaux']=cases
    stats['full_enlarged_radix_legal_tableaux']=valid

full_tableau_checks()
report['counts']=stats
(HERE/'independent-check-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'additional_full_tableau_counts': {k:v for k,v in stats.items() if k.startswith('full_')}},indent=2))


def explicit_fixtures():
    b=1024; A=8; B=C=4; N=A*B*C
    X=b**A; Y=b**(A*B); Q=b**N
    j=4+A*2+A*B*2
    point=b**j; second=point*b
    def check(eta,layers):
        pre=E=slack=0; counts=[0,0]; physical_legal=True
        for t,ev in enumerate(layers):
            pre+=(counts[0]*point+counts[1]*second)*Q**t
            E+=(ev[0]*point+ev[1]*second)*Q**t
            counts=[counts[i]+ev[i] for i in range(2)]
        K=len(layers); R=geometric(Q,K); final=counts[0]*point+counts[1]*second
        assert Q*(pre+E)==pre+Q**K*final
        available=eta*R+b*pre+X*pre+Y*pre+pre//b+pre//X+pre//Y
        selected=available&((b-1)*E)
        own=pre&((b-1)*E)
        slack=selected-6*own-6*E
        legal=slack>=0 and slack&((b//2-1)*E)==slack
        return legal,E,final,slack
    legal,E,V,S=check(12*point+4*second,((1,0),(1,0),(0,1)))
    assert legal and V==2*point+second
    assert E&(second*Q**2)==second*Q**2
    assert E&point==point and V&point==0  # even final target count
    assert check(5*point+5*second,((1,0),))[0] is False
    assert check(5*point+5*second,((0,1),))[0] is False
    assert check(5*point+5*second,((1,1),))[0] is False
    assert check(6*point,((1,0),(1,0)))[0] is False
    all_fives=5*geometric(b,N)
    assert check(all_fives+point,((1,0),))[0] is True
    # Negative control suggested by the parent: an actual false certificate
    # if the lower-half mask were incorrectly widened to a full radix digit.
    legal,E,V,S=check(7*second,((1,1),))
    assert S==(b-6)*point
    assert 6*E+S==7*second
    assert S&((b-1)*E)==S
    assert S&((b//2-1)*E)!=S
    assert legal is False
    # The only legal first firing for [0,7] sends one chip to the zero site
    # and leaves every site below threshold; target zero cannot ever fire.
    assert 0+1<6 and 7-6<6
    stats['explicit_fixtures']={
      'repeated_prefix_12_4':'accepted',
      'even_final_count_target':'event accepted; low final bit absent',
      'all_nonempty_first_layers_5_5':'rejected',
      'unsupported_second_own_firing_6_0':'rejected',
      'height_five_background_plus_one':'one-event certificate accepted',
      'full_slack_false_positive_negative_control_0_7':'counterfeit full-mask witness accepted by relaxed mask, rejected by original half-mask'
    }

explicit_fixtures()
report['counts']=stats
(HERE/'independent-check-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'explicit_fixtures':stats['explicit_fixtures']},indent=2))
