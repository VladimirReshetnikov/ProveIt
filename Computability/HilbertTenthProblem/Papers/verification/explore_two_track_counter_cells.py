#!/usr/bin/env python3
"""Exact finite checks for the conditional two-track counter-cell component."""
from itertools import product
from pathlib import Path
import json


def residuals(bits, decrement=False):
    a0,a1,c,b0,b1,d,e=bits
    if decrement:
        return a0+2*d-b0-c, a1+2*e-b1-d
    return a0+c-b0-2*d, a1+d-b1-2*e


def expected(a0,a1,c,decrement=False):
    value=a0+2*a1
    result=value-c if decrement else value+c
    d=int(a0<c) if decrement else (a0+c)//2
    e=int(value<c) if decrement else result//4
    return result%2,(result%4)//2,d,e


def tracks(value):
    first=second=0
    place=1
    while value:
        value,digit=divmod(value,4)
        first+=(digit%2)*place
        second+=(digit//2)*place
        place*=4
    assert first+2*second >= 0
    return first,second


def verify():
    assignments=list(product(range(2),repeat=7))
    scalar_cases=packed_cases=ripple_cases=0
    for decrement in (False,True):
        multiplicity={inputs:0 for inputs in product(range(2),repeat=3)}
        for bits in assignments:
            a0,a1,c,b0,b1,d,e=bits
            holds=residuals(bits,decrement)==(0,0)
            assert holds == ((b0,b1,d,e)==expected(a0,a1,c,decrement))
            if holds:
                multiplicity[(a0,a1,c)]+=1
            scalar_cases+=1
        assert set(multiplicity.values())=={1}
        for low in assignments:
            for high in assignments:
                packed=tuple(x+4*y for x,y in zip(low,high))
                holds=residuals(packed,decrement)==(0,0)
                assert holds == (residuals(low,decrement)==(0,0)
                                 and residuals(high,decrement)==(0,0))
                packed_cases+=1
        for width in range(1,5):
            for value in range(4**width):
                carry=1
                output=0
                incoming=internal=outgoing=0
                for j in range(width):
                    digit=(value//4**j)%4
                    a0,a1=digit%2,digit//2
                    b0,b1,d,e=expected(a0,a1,carry,decrement)
                    assert residuals((a0,a1,carry,b0,b1,d,e),decrement)==(0,0)
                    incoming+=carry*4**j
                    internal+=d*4**j
                    outgoing+=e*4**j
                    output+=(b0+2*b1)*4**j
                    carry=e
                initial_tracks=tracks(value)
                final_tracks=tracks(output)
                assert value==initial_tracks[0]+2*initial_tracks[1]
                assert output==final_tracks[0]+2*final_tracks[1]
                assert incoming==1+4*outgoing-carry*4**width
                packed=(*initial_tracks,incoming,*final_tracks,internal,outgoing)
                assert residuals(packed,decrement)==(0,0)
                target=value-1 if decrement else value+1
                assert output==target%4**width
                assert carry==(int(value==0) if decrement else int(value==4**width-1))
                ripple_cases+=1
    return dict(status='PASS_LOCAL_COMPONENT_ONLY',scalar_assignments=scalar_cases,
                complete_two_cell_assignments=packed_cases,ripple_chains=ripple_cases,
                maximum_counter_bits=8,local_operations=6,
                local_histogram={'*':2,'+':4},raw_input_link_operations=2,
                scope='Exact Boolean increment/decrement arithmetic cells and raw input link; shared control, zero-branch routing, masks, positive adapters and complete history are unconstructed.',
                proof='../1980/EXPLORATION_TWO_TRACK_COUNTER_CELLS.md')


if __name__=='__main__':
    receipt=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(receipt,indent=2))
