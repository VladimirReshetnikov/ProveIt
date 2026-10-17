#!/usr/bin/env python3
"""Independent syntax/order audit of the exact Enum254 candidate stream.

This does not simulate registers or a Turing machine. It checks decoding,
encoding, the marked NIP-to-DROP injection, and every command-prefix count
for an initial finite interval of candidate numbers.
"""
import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path


def pair(a, b):
    return b + (a+b)*(a+b+1)//2


def unpair(n):
    diagonal = (isqrt(8*n+1)-1)//2
    b = n-diagonal*(diagonal+1)//2
    return diagonal-b, b


def decode(n):
    out = []
    while True:
        old = n
        opcode, rest = unpair(n)
        fields = []
        for _ in range(3 if opcode >= 3 else 1):
            a, rest = unpair(rest)
            fields.append(a)
        out.append((opcode, *fields))
        if rest == 0:
            return out
        n = rest-1
        assert n < old, 'Candidate suffix failed to decrease'


def encode(commands):
    assert commands
    result = None
    for command in reversed(commands):
        rest = 0 if result is None else result+1
        for field in reversed(command[1:]):
            rest = pair(field, rest)
        result = pair(command[0], rest)
    return result


def audit(limit):
    specification = {'pairing':'b+(a+b)*(a+b+1)//2',
                     'opcode_field_counts':{'0':1,'1':1,'2':1,'at_least_3':3},
                     'suffix_pointer':'zero for end; otherwise suffix_code+1',
                     'first_candidate':0,'candidate_count':limit}
    drops = set()
    images = set()
    counts = {'MP':0, 'DROP':0, 'NIP':0, 'AX':0}
    minimum_pre_nip_margin = None
    deepest_occurrence = 0
    for n in range(limit):
        commands = decode(n)
        assert encode(commands) == n
        for i, command in enumerate(commands):
            op = command[0]
            if op == 2:
                replaced = list(commands)
                replaced[i] = (1, *command[1:])
                m = encode(replaced)
                assert m < n
                assert decode(m) == replaced
                image = (m, i)
                assert image in drops, 'Image DROP was not already executed'
                assert image not in images, 'Marked-occurrence map collided'
                images.add(image)
                margin = counts['DROP']-counts['NIP']
                assert margin >= 1, 'A NIP can expose the initial stack'
                minimum_pre_nip_margin = margin if minimum_pre_nip_margin is None else min(minimum_pre_nip_margin, margin)
                deepest_occurrence = max(deepest_occurrence, i)
            if op == 1:
                drops.add((n,i))
            counts[['MP','DROP','NIP'][op] if op < 3 else 'AX'] += 1
            assert counts['DROP'] >= counts['NIP']

    # The occurrence mark cannot be omitted from the injection's codomain.
    left = [(2,0),(1,0)]
    right = [(1,0),(2,0)]
    common = [(1,0),(1,0)]
    assert encode(common) < min(encode(left),encode(right))
    assert left != right
    nested_examples = [
        [(3,0,0,0),(2,0)],
        [(7,1,2,3),(0,4),(1,3),(3,0,0,0),(2,2)],
        [(1,0),(4,0,1,0),(2,1),(3,0,0,0),(2,0)],
    ]
    specification['constructed_nested_controls'] = nested_examples
    nested_results = []
    for commands in nested_examples:
        n = encode(commands)
        assert decode(n) == commands
        checked = []
        for i, command in enumerate(commands):
            if command[0] != 2:
                continue
            replaced = list(commands)
            replaced[i] = (1,*command[1:])
            m = encode(replaced)
            assert m < n and decode(m) == replaced
            recovered = decode(m)
            recovered[i] = (2,*recovered[i][1:])
            assert encode(recovered) == n
            checked.append(i)
        nested_results.append({'commands':commands,'candidate_code_bits':n.bit_length(),
                               'checked_nip_positions':checked,
                               'inverse_recovered_original':True})
    result = {
        'scope':'candidate syntax and global DROP/NIP prefix counts only; no machine or formula simulation',
        'candidate_count':limit,
        'input_specification':specification,
        'input_specification_sha256':hashlib.sha256(json.dumps(specification,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        'candidates_start_at':0,
        'command_counts':counts,
        'total_commands':sum(counts.values()),
        'checked_marked_nip_images':len(images),
        'minimum_drop_minus_nip_before_nip':minimum_pre_nip_margin,
        'maximum_nip_position_zero_based':deepest_occurrence,
        'round_trips_exact':True,
        'all_marked_images_strictly_earlier':True,
        'all_marked_images_injective':True,
        'all_prefix_drop_counts_dominate':True,
        'constructed_nested_arity_controls':nested_results,
        'unmarked_collision_example':{
            'left_candidate':encode(left),
            'left_mark':0,
            'right_candidate':encode(right),
            'right_mark':1,
            'common_image_candidate':encode(common),
            'distinct_image_marks':[0,1]
        }
    }
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--candidates',type=int,default=100000)
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('drop_barrier_check.json'))
    a = p.parse_args()
    if a.candidates < 1:
        p.error('at least one candidate is required')
    result = audit(a.candidates)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
