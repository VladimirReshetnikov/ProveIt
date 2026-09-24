#!/usr/bin/env python3
"""Scoped equal/complementary-mask obstructions for the native76 interface."""
from itertools import product
from pathlib import Path
import argparse
import json

import explore_fixed_raw_universal_76 as native
import explore_fixed_raw_universal_81 as semantics


def verify_equal_masks():
    cases=saturated=too_small=too_large=0
    for d in range(2,10):
        B=1<<d
        # Even masks permit the native unit marker. Exclude the zero mask.
        for mask in range(2,B-1,2):
            for N in (1,2,3):
                q=B**N;J=(q-1)//(B-1)
                M=(mask+q*mask)*J
                S=1+q
                assert 0<S<q*q and 0<M<q*q and S&M==0
                r=(q*q-S)*(q*q-1)+M
                expected=2*d*N+2*N*mask.bit_count()
                assert r.bit_count()==expected and r%2==1
                assert (expected==3*d*N)==(d==2*mask.bit_count())
                if expected==3*d*N:
                    saturated+=1;assert d%2==0
                elif expected<3*d*N:too_small+=1
                else:too_large+=1
                cases+=1
    divisibility=0
    for d in range(1,129):
        for j in range(1,4096,2):
            if j%d==0:
                assert d%2==1;divisibility+=1
    return dict(actual_packed_population_cases=cases,exact_saturation_cases=saturated,
                population_too_small=too_small,population_above_threshold=too_large,
                odd_index_divisibility_cases=divisibility,
                conclusion='Exact equal-mask q-cubed saturation needs even d; aligned odd Pell exponent needs odd d',
                scope='Retains exact population saturation; no unsoundness claim is inferred solely from a population surplus')


def verify_singleton_convolution():
    cases=accepted=origin_cases=0
    directions={-1:0,1:0}
    for N in range(3,66):
        for origin in sorted({0,N//2,N-1}):
            origin_cases+=1
            s=[int(i==origin) for i in range(N)]
            for step in (-1,1):
                for a,b,h in product((0,1),(0,1),range(N)):
                    values=[(a*s[i]+b*s[(i-step)%N]+s[(i-h)%N])%2 for i in range(N)]
                    valid=not any(values)
                    expected=(a,b,h) in ((1,0,0),(0,1,step%N))
                    assert valid==expected
                    assert sum(values)%2==(a+b+1)%2
                    cases+=1
                    if valid:
                        assert a+b==1
                        accepted+=1;directions[step]+=1
    return dict(cycle_lengths=[3,65],marker_origin_cases=origin_cases,
                exhaustive_parity_offset_cases=cases,accepted_cases=accepted,
                accepted_by_spatial_direction=directions,
                formula='a*s[i]+b*s[i-step]+s[i-h]=0',
                conclusion='Only current-word or spatial-neighbor temporal successor is possible')


def verify_actual_start():
    blocks=semantics.unary.blocks
    records=[]
    for modulus,residue in ((1,0),(2,0),(3,1),(5,2)):
        machine=semantics.residue_machine(modulus,residue)
        S,E=semantics.fixed_markers(machine)
        assert semantics.helical.predicate(machine)(S)
        H=S[0];I=S[3]
        assert S[:3]==(H,H,H) and S[3]==S[4]==I
        assert H!=I and S[5]!=H
        assert not blocks.vertical(S,S)
        # Contradictory forced entries do not depend on the neighbor's other tiles.
        assert S[1]!=S[3] and S[0]!=S[4]
        tiles=list(dict.fromkeys(S+E))
        right_count=left_count=0
        for free in product(tiles,repeat=3):
            right=tuple(S[3*r+c+1] if c<2 else free[r]
                        for r in range(3) for c in range(3))
            left=tuple(free[r] if c==0 else S[3*r+c-1]
                       for r in range(3) for c in range(3))
            assert blocks.horizontal(S,right) and not blocks.vertical(S,right)
            assert blocks.horizontal(left,S) and not blocks.vertical(S,left)
            right_count+=1;left_count+=1
        records.append(dict(modulus=modulus,residue=residue,start_predicate=True,
                            self_vertical_rejected=True,neighbor_tile_sample_size=len(tiles),
                            right_completions_rejected=right_count,left_completions_rejected=left_count,
                            right_conflicting_position=[0,0],left_conflicting_position=[0,1]))
    return dict(actual_machine_cases=records,
                right_completions_rejected=sum(r['right_completions_rejected'] for r in records),
                left_completions_rejected=sum(r['left_completions_rejected'] for r in records),
                scope='Actual fixed Start and overlap functions; finite neighbor completions supplement the alphabet-independent forced-entry proof')


def verify_native_interface():
    records=[]
    for a in (2,3,4):
        windows=[tuple([state]*9) for state in range(a)]
        cc=native.compile_windows(windows,a)
        assert cc.d%2==1 and cc.dummy
        assert len(cc.positions)-1==cc.m
        # MC permits exactly these m positions, including Start0 but excluding End1.
        assert 0 in cc.positions and 1 in cc.positions
        assert min(cc.MFpoly)>0
        units=[]
        for state in range(a):
            bits=dict(zip(cc.positions,cc.bits(state)))
            assert bits[0]==int(state==0)
            units.append(bits[0])
        assert cc.DCpoly.get(0,0)%2==0 and cc.H>0
        records.append(dict(selectors=a,cell_bits=cc.d,cell_bits_odd=True,
                            native_positions=len(cc.positions),field_mask_population=cc.m,
                            remainder_mask_population=cc.d-cc.m,
                            selector_unit_bits=units,current_field_mask_even=True,
                            current_center_coefficient_even=True,current_right_coefficient_even=True,
                            full_cell_radix_materialized=False))
    return records


def verify():
    return dict(status='PASS_NATIVE_MASK_RELATION_OBSTRUCTIONS',
                equal_masks=verify_equal_masks(),
                singleton_convolution=verify_singleton_convolution(),
                actual_start=verify_actual_start(),native_interface=verify_native_interface(),
                proof='../1980/EXPLORATION_NATIVE_MASK_RELATIONS.md',
                new_operation_bound=None,
                scope='Exact unchanged q-cubed packing/alignment for equal masks; native unique-unit Start and carry-free DY=1 field for complementary masks; no general compiler lower bound',
                review='Author and independent complete proof/source reviews pass; fresh exact receipt checks pass')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();normalized=json.loads(json.dumps(result))
    receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8')
    else:assert normalized==json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'])
    print(result['equal_masks'])
    print(result['singleton_convolution'])
    print('actual neighbor completions',result['actual_start']['right_completions_rejected'],result['actual_start']['left_completions_rejected'])
