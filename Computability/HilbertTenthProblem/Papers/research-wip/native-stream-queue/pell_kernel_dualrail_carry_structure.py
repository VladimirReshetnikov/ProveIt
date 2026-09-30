"""Necessary conditions for the filtered dual-rail carry/FIFO architecture."""
import argparse
from itertools import product
import json
from pathlib import Path


def centered_interval(coefficients,cs,h):
    P=sum(max(c,0) for c in coefficients)
    N=sum(max(-c,0) for c in coefficients)
    return min(2*cs-h,-N),max(2*cs-h,P)


def terminal_width_bound(read,append,cs,cf,h=0):
    coefficients=read+append
    low,high=centered_interval(coefficients,cs,h)
    PR=sum(max(c,0) for c in read)
    NR=sum(max(-c,0) for c in read)
    target=2*cf-h
    if target < -NR:
        return (-low-NR)//(-target-NR)
    if target > PR:
        return (high-PR)//(target-PR)
    return None


def same_sign_input_bound(read,append,cs,cf,h=0):
    if read[0]*read[1]<=0:
        return None
    sign=1 if read[0]>0 else -1
    if sign*(2*cf-h)>0:
        return None
    m=min(sign*c for c in read)
    b=min(sign*c for c in append)
    return max(2*max(0,-b),abs(2*cs-h))//(2*m)


def terminal_blocks():
    systems=paths=accepted=bounded=endpoint=0
    for coefficients in product(range(-1,2),repeat=4):
        read,append=coefficients[:2],coefficients[2:]
        PR=sum(max(c,0) for c in read);NR=sum(max(-c,0) for c in read)
        for cs,cf,h in product(range(-2,3),repeat=3):
            systems+=1
            low,high=centered_interval(coefficients,cs,h)
            target=2*cf-h
            bound=terminal_width_bound(read,append,cs,cf,h)
            for m in range(1,4):
                W=3**m
                for entry in range(-((-(low+h))//2),(high+h)//2+1):
                    for labels in product(range(4),repeat=m):
                        carry=entry;increments=[]
                        for label in labels:
                            increment=read[0]*(label&1)+read[1]*((label>>1)&1)
                            numerator=carry+h+increment
                            if numerator%3:break
                            carry=numerator//3;increments.append(increment)
                        else:
                            paths+=1
                            assert W*(2*carry-h)>=2*entry-h-NR*(W-1)
                            assert W*(2*carry-h)<=2*entry-h+PR*(W-1)
                            if carry!=cf:continue
                            accepted+=1
                            if bound is not None:
                                assert W<=bound
                                bounded+=1
                            if target==-NR:
                                weighted=sum((g+NR)*3**j for j,g in enumerate(increments))
                                assert 2*weighted==-2*entry+h-NR<=-low-NR
                                endpoint+=1
                            if target==PR:
                                weighted=sum((PR-g)*3**j for j,g in enumerate(increments))
                                assert 2*weighted==2*entry-h-PR<=high-PR
                                endpoint+=1
    assert systems and paths and accepted and bounded and endpoint
    return dict(coefficient_state_systems=systems,integral_read_only_paths=paths,
                accepted_terminal_blocks=accepted,accepted_with_finite_width_bound=bounded,
                endpoint_deficit_checks=endpoint,maximum_terminal_block_length=3)


def dominance_bound():
    inequalities=0;systems=0
    for coefficients in product(range(-2,3),repeat=4):
        read,append=coefficients[:2],coefficients[2:]
        for cs,cf,h in product(range(-2,3),repeat=3):
            bound=same_sign_input_bound(read,append,cs,cf,h)
            if bound is None:continue
            systems+=1
            sign=1 if read[0]>0 else -1
            m=min(sign*c for c in read);b=min(sign*c for c in append)
            for I in range(max(1,bound+1),max(1,bound+1)+4):
                for W in range(I+1,I+4):
                    for A in range(4):
                        assert 2*m*I+2*(m*W+b)*A+sign*(2*cs-h)>0
                        assert sign*(2*cf-h)<=0
                        inequalities+=1
    return dict(same_sign_coefficient_state_systems=systems,strict_lower_bounds_checked=inequalities)


def last_append_block():
    # Exact transport D=I+WA<q implies A<q/W, so its last m trits
    # are zero independently of any controller or chosen rail orientation.
    checked=0
    for m in range(1,4):
        W=3**m
        for t in range(m,m+4):
            q=3**t
            for I in range(1,W):
                for A in range((q-I-1)//W+1):
                    D=I+W*A
                    assert D<q and A<3**(t-m)
                    assert all(A//3**j%3==0 for j in range(t-m,t))
                    checked+=1
    return dict(positive_initial_queue_transport_tuples=checked,maximum_width_exponent=3)


def verify():
    return dict(status='PASS_DUALRAIL_CARRY_NECESSARY_CONDITIONS',
                terminal_blocks=terminal_blocks(),dominance=dominance_bound(),
                terminal_zero_append=last_append_block(),
                affine_offset='Arbitrary fixed integer h and arbitrary fixed integer endpoints cs,cf',
                scope='Necessary coefficient/input bounds and endpoint rigidity only; not a universality or decidability theorem',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps(result,indent=2))
