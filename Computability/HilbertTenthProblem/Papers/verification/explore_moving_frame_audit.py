#!/usr/bin/env python3
"""Independent finite checks of moving fronts and fixed-prefix decidability."""
from pathlib import Path
import json


def local(a,b,c):
    return (110 >> (4*a+2*b+c)) & 1


def step(word):
    assert word > 0
    result=0
    for i in range(word.bit_length()+1):
        a=(word>>(i-2))&1 if i>=2 else 0
        b=(word>>(i-1))&1 if i>=1 else 0
        c=(word>>i)&1
        result|=local(a,b,c)<<i
    assert result > 0
    return result


def prefix_step(word,width):
    result=0
    for i in range(width):
        a=(word>>(i-2))&1 if i>=2 else 0
        b=(word>>(i-1))&1 if i>=1 else 0
        c=(word>>i)&1
        result|=local(a,b,c)<<i
    return result


def triple(word):
    return bool(word & (word>>1) & (word>>2))


def verify():
    run_cases=front_cases=prefix_cases=orbit_cases=0
    maximum_transient_cycle=0
    for word in range(1,2**12):
        state=word
        seen=triple(state)
        original_left=(word&-word).bit_length()-1
        original_right=word.bit_length()-1
        for t in range(1,4):
            state=step(state)
            assert (state&-state).bit_length()-1 == original_left
            assert state.bit_length()-1 == original_right+t
            if t<=2:
                seen|=triple(state)
            front_cases+=1
        assert seen
        run_cases+=1
    for width in range(1,9):
        mask=2**width-1
        for low in range(2**width):
            expected=prefix_step(low,width)
            for high in range(16):
                word=low+(high<<width)
                if word:
                    assert step(word)&mask == expected
                else:
                    assert expected==0
                prefix_cases+=1
            state=low
            seen={}
            while state not in seen:
                seen[state]=len(seen)
                state=prefix_step(state,width)
            assert len(seen)<=2**width
            maximum_transient_cycle=max(maximum_transient_cycle,len(seen))
            orbit_cases+=1
    return dict(status='MOVING_FRAME_AUDIT_CHECKS_PASS',universality_status='NOT_CLAIMED',
                nonempty_words_checked=run_cases,maximum_initial_digits=12,
                front_identity_steps=front_cases,higher_prefix_extensions=prefix_cases,
                finite_prefix_orbits=orbit_cases,maximum_orbit_states_seen=maximum_transient_cycle,
                scope='Finite checks of111within2steps, moving fronts, autonomous prefixes and orbit termination. No universal representation or complete huge Pell tuple is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
