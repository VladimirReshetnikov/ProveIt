"""One fixed universal positive-input polynomial through the U15 tag route.

The huge fixed coefficients have exact finite recipes, not extra variables.
No production word, giant fixed integer, or full Pell zero is expanded.
"""
import argparse
from bisect import bisect_left
import hashlib
import json
from pathlib import Path
import random

import neary_woods_u15_tag_metadata as metadata
import binary_tag_parameterized_compressed_compiler as compiler


def production_letter(table, counts, position):
    """Exact random access to the fixed interleaved production u.

    This is a coefficient recipe, never an arithmetic operation of the
    polynomial and never dependent on its input/program/witness tuple.
    """
    p, beta, s = table['p'], counts['beta'], counts['s']
    assert 0 <= position < beta*s
    row, track = divmod(position, beta)
    residue = track % 10
    if residue % 2 == 0 or residue == 9:
        return 'b'
    if residue == 1:
        return 'c'
    shift = {7: 4, 5: 6, 3: 8}[residue]
    m = ((1-track-shift)//10) % p
    assert (beta-10*m+1-shift) % beta == track
    alpha = table['rows'].get(m, metadata.Word(0))
    garbage = residue in (5, 7) or (m == 0 and alpha.length == 0)
    if not garbage and m == table['halt']:
        return 'b' if row == 0 else 'c'
    index = row+(m == 0)
    length = p if garbage else alpha.length
    if index >= 11*length:
        return 'c'
    bit_index, local = divmod(index, 11)
    if garbage:
        char = 'e'
    else:
        place = bisect_left(alpha.ones, bit_index)
        char = '1' if place < len(alpha.ones) and alpha.ones[place] == bit_index else '0'
    return metadata.tag.THETA[char][local]


def components():
    machine, binary, rules = metadata.compiled_u15()
    machine_ledger = metadata.cw.ledger(machine, binary)
    table = metadata.cts_table(machine_ledger['binary_states'], rules)
    summary = metadata.row_summary(table)
    counts = metadata.track_counts(table['p'], table['total_length'], summary['maximum'])
    D = 256*table['z']*counts['bit_block_length']
    assert D == 911894954830740789802965708213760
    assert D.bit_length()+D.bit_count()-2 == 160
    binary_wire = [[i, bit, write, target] for (i, bit), (write, target) in sorted(rules.items())]
    recipe = dict(binary_table_sha256=hashlib.sha256(json.dumps(binary_wire).encode()).hexdigest(),
        cts_sparse_table_sha256=summary['sparse_table_sha256'],
        state_numbering='start first, remaining nonhalt states by repr, halt last',
        binary_start='read(run(u1),empty_prefix)', Q=table['Q'], z=table['z'], p=table['p'],
        halt=table['halt'], beta=counts['beta'], s=counts['s'],
        u_definition='Interleave the fixed tracks: u[beta*i+j]=track_j[i]. '
                     'production_letter(table,counts,k) specifies every letter exactly.',
        production_offset_definition='val(1 e(u without its last b) 10), e(b)=10^beta1,e(c)=1',
        encoded_production_length=counts['e_u_length'], D=D)
    return table, counts, machine_ledger, summary, recipe


def build(form='normalized'):
    table, counts, machine, summary, recipe = components()
    packet = compiler.build(recipe['D'], counts['beta'], counts['e_u_length'], form)
    return packet, dict(machine=machine, cts=summary, tag_counts=counts, fixed_recipe=recipe)


def verify():
    rng = random.Random(557351206)
    samples = 0
    # Compare the random-access fixed-word definition with the independently
    # materialized earlier track compiler on small arbitrary tables.
    for p in range(2,10):
        for case in range(4):
            alphas = [''.join(rng.choice('01') for _ in range(p if i in (0,p-1) else rng.randrange(9)))
                      for i in range(p)]
            small = dict(p=p, halt=p-1, rows={i: metadata.Word(len(w), tuple(j for j,b in enumerate(w) if b=='1'))
                                            for i,w in enumerate(alphas)})
            literal = metadata.tag.build_tracks(alphas,p-1)
            word = metadata.tag.materialize(literal)
            counts = dict(beta=literal['beta'], s=literal['s'])
            for k in sorted({0, 1, 2, len(word)-1}|{rng.randrange(len(word)) for _ in range(60)}):
                assert production_letter(small,counts,k) == word[k]
                samples += 1
    table, counts, machine, summary, recipe = components()
    assert ''.join(production_letter(table,counts,j) for j in range(3)) == 'bcb'
    assert production_letter(table,counts,counts['u_length']-1) == 'b'
    assert (counts['u_length']-1) % (counts['beta']-1) == 0
    assert recipe['encoded_production_length']-counts['beta']+1 >= counts['beta']+3
    assert recipe['D'] % (table['z']*counts['bit_block_length']) == 0
    assert recipe['D']//(table['z']*counts['bit_block_length']) == 256
    ledgers = []
    for form in ('raw', 'units', 'normalized'):
        packet = compiler.build(recipe['D'], counts['beta'], counts['e_u_length'], form)
        ledgers.append(compiler.ledger(packet))
    assert [p['polynomial']['operations'] for p in ledgers] == [635, 560, 557]
    assert ledgers[-1]['polynomial']['multiplications'] == 351
    assert ledgers[-1]['polynomial']['additions_subtractions'] == 206
    source, out = compiler.parent.polynomial_source(packet)
    encoded_source = compiler.encode_source(source)
    # Exact counter boundary, tested independently of the huge word constants.
    counter_checks = 0
    for overhead in (1, 8, 127, 128, 129, 1000, 100001):
        bound = max(1, (overhead+127)//128)
        for extra in (0,1,3):
            n = 1 << (bound.bit_length()+extra)
            assert n > bound
            tape_length = 128*n+overhead
            assert 128*n < tape_length < 256*n
            assert 1 << (tape_length-1).bit_length() == 256*n
            counter_checks += 1
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_TAG557',
        machine=machine, cts=summary, tag_counts=counts, fixed_recipe=recipe,
        ledgers=ledgers, coefficient_recipe_letter_checks=samples,
        exact_initial_counter_checks=counter_checks,
        example=dict(source=encoded_source, output=out, parameters=packet['parameters'],
                     auxiliaries=packet['auxiliaries'], comparisons=packet['comparisons'],
                     fixed_numeral_definitions=compiler.NUMERALS),
        source_sha256=hashlib.sha256(json.dumps(encoded_source,sort_keys=True).encode()).hexdigest(),
        scope='A fixed universal polynomial on positive inputs, with five positive program '
              'parameters, 69 positive existential witnesses, and a charged 557-operation '
              'source. Fixed numerals use exact finite recipes. Degree upper bound only; '
              'no expanded universal tag word, giant numeral, full Pell zero or Lean proof.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result,indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['ledgers'][-1])
