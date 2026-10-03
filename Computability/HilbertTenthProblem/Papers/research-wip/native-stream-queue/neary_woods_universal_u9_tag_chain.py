"""The explicit U9 tag polynomial with a 127-multiplication exponent chain.

Four positive program coefficients include the paid duration bound. All huge
fixed numerals retain exact finite recipes; none are materialized here.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_u9_tag_metadata as metadata
import neary_woods_universal_tag557 as u15
import neary_woods_universal_tag_chain as schedule

compiler = schedule.compiler
D = 47946621298704238734708993009920


def components():
    machine, binary, rules = metadata.compiled_u9()
    ledger = metadata.cw.ledger(machine, binary)
    table = metadata.metadata.cts_table(ledger['binary_states'], rules)
    summary = metadata.metadata.row_summary(table)
    counts = metadata.metadata.track_counts(table['p'], table['total_length'], summary['maximum'])
    assert D == metadata.D_EXPECTED == 128*table['z']*counts['bit_block_length']
    wire = [[i, bit, write, target] for (i, bit), (write, target) in sorted(rules.items())]
    recipe = dict(machine='Neary-Woods U9 Table4 with the sole missing instruction adapted to accept',
        source_renaming={'c': '_', 'b': '0', 'delta': '1'},
        binary_table_sha256=hashlib.sha256(json.dumps(wire).encode()).hexdigest(),
        cts_sparse_table_sha256=summary['sparse_table_sha256'],
        state_numbering='start first, remaining nonhalt states by repr, halt last',
        binary_start='read(run(u1),empty_prefix)', Q=table['Q'], z=table['z'], p=table['p'],
        halt=table['halt'], beta=counts['beta'], s=counts['s'],
        u_definition='Interleave the fixed tracks: u[beta*i+j]=track_j[i]. '
                     'The imported production_letter(table,counts,k) specifies every letter.',
        production_offset_definition='val(1 e(u without its last b) 10), e(b)=10^beta1,e(c)=1',
        encoded_production_length=counts['e_u_length'], D=D)
    return table, counts, ledger, summary, recipe


def build(form='normalized', *, merge_bound=True):
    assert form in ('raw', 'units', 'normalized')
    table, counts, machine, summary, recipe = components()
    packet = schedule.rewrite_raw(
        compiler.raw_build(D, counts['beta'], counts['e_u_length']),
        merge_bound=merge_bound, chain=metadata.power_chain())
    if form != 'raw':
        packet = compiler.parent.units.rewrite(packet)
        packet.update(form='units', unit_product=True)
        if form == 'normalized':
            packet = compiler.parent.normalized.rewrite(packet)
            packet['form'] = form
    compiler.check_source(packet)
    return packet


def ledger(packet):
    source, out = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    base, witnesses, equations = {'raw': (475, 88, 56),
                                 'units': (400, 69, 28),
                                 'normalized': (397, 69, 25)}[packet['form']]
    chain = metadata.power_chain()
    assert packet['width'] == D and len(chain) == 127
    assert len(source) == base+len(chain)
    assert (packet['witnesses'], packet['equations']) == (witnesses, equations)
    expected_parameters = [n for n in compiler.PARAMETERS
                           if not (packet['bound_is_program_E'] and n == 'program_bound')]
    assert packet['parameters'] == expected_parameters
    return dict(form=packet['form'], width=D, power_chain_operations=len(chain),
        saved_multiplications_vs_binary=154-len(chain),
        certificate={k: packet[k] for k in ('operations', 'multiplications',
                     'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=out),
        parameters=packet['parameters'], bound_is_program_E=packet['bound_is_program_E'],
        **compiler.degree_upper_bound(packet))


def verify():
    table, counts, machine, summary, recipe = components()
    assert (table['Q'], table['z'], table['p']) == (1968, 59101, 118202)
    assert counts['beta'] == 1182020 and counts['s'] == 5910096
    assert ''.join(u15.production_letter(table, counts, j) for j in range(3)) == 'bcb'
    assert u15.production_letter(table, counts, counts['u_length']-1) == 'b'
    assert (counts['u_length']-1) % (counts['beta']-1) == 0
    assert counts['e_u_length']-counts['beta']+1 >= counts['beta']+3
    assert D.bit_length() == 106 and D.bit_count() == 50
    chain = metadata.power_chain()
    source = schedule.chain_source(chain, D)
    assert chain[115][0] == 37458297889612686511491400789
    assert chain[118][0] == 5*chain[115][0]
    assert D == (1 << 8)*5*chain[115][0]
    rng = random.Random(524318206)
    powers = 0
    for modulus in (2, 8, 27, 97, 257, 1009, 65537, 1000000007):
        for q in (-100, -19, -2, -1, 0, 1, 2, 3, 16, 97, modulus, modulus+1):
            env = schedule.execute_mod(source, {'q': q}, {}, modulus)
            for exponent, _, _ in chain:
                name = 'Q' if exponent == D else f'addition_power{exponent}'
                assert env[name] == pow(q, exponent, modulus)
            powers += 1
    # Independent forward track addresses for the actual U9 production;
    # no inverse-residue calculation from production_letter is reused.
    letter_checks = 0
    p, beta, s = table['p'], counts['beta'], counts['s']
    for j in {0, 1, table['halt'], p-1}|{rng.randrange(p) for _ in range(128)}:
        zm = (beta-10*j+1) % beta
        for offset in (4, 6, 8):
            word = table['rows'].get(j, metadata.metadata.Word(0))
            garbage = offset != 8 or (j == 0 and word.length == 0)
            short_length = 11*(p if garbage else word.length)
            rows = {0, 1, 4, 6, 8, 10, s-1, max(0, short_length-2),
                    min(s-1, short_length), rng.randrange(s)}
            for row in rows:
                if offset == 8 and j == table['halt']:
                    expected = 'b' if row == 0 else 'c'
                else:
                    index = row+(j == 0)
                    if index >= short_length:
                        expected = 'c'
                    else:
                        bit, local = divmod(index, 11)
                        cpos = 4 if garbage else 8 if bit in word.ones else 6
                        expected = 'c' if local == cpos else 'b'
                assert u15.production_letter(table, counts, beta*row+(zm-offset) % beta) == expected
                letter_checks += 1
    records = []
    identities = signed = 0
    for form in ('raw', 'units', 'normalized'):
        old = compiler.build(D, counts['beta'], counts['e_u_length'], form)
        osource, oout = compiler.parent.polynomial_source(old)
        for merge_bound in (False, True):
            packet = build(form, merge_bound=merge_bound)
            newsource, newout = compiler.parent.polynomial_source(packet)
            assert packet['auxiliaries'] == old['auxiliaries']
            assert packet['comparisons'] == old['comparisons']
            common = {n for n, _, _, _ in osource} & {n for n, _, _, _ in newsource}
            for case in range(128):
                modulus = (257, 65537, 1000000007, 1048576)[case % 4]
                values = {n: rng.randrange(1, 20) if case < 64 else rng.randrange(-20, 21)
                          for n in packet['parameters']+packet['auxiliaries']}
                constants = {n: rng.randrange(-1000, 1001) for n in compiler.NUMERALS}
                restored = dict(values)
                if merge_bound:
                    restored['program_bound'] = values['program_E']
                before = schedule.execute_mod(osource, restored, constants, modulus)
                after = schedule.execute_mod(newsource, values, constants, modulus)
                assert all(before[n] == after[n] for n in common)
                assert before[oout] == after[newout]
                identities += 1
                signed += case >= 64
            records.append(ledger(packet))
    counter_cases = 0
    for _ in range(96):
        prefix = ''.join(rng.choice('01') for _ in range(rng.randrange(1, 25)))
        middle = ''.join(rng.choice('01') for _ in range(rng.randrange(1, 25)))
        tail = ''.join(rng.choice('01') for _ in range(rng.randrange(1, 25)))
        E = int('1'+prefix+middle+tail, 2)
        overhead = rng.randrange(1, len(prefix)+len(middle)+1)
        n = 1 << E.bit_length()
        assert E >= overhead and n > E and n > (overhead+63)//64
        tape_length = 64*n+overhead
        assert 64*n < tape_length < 128*n
        assert 1 << (tape_length-1).bit_length() == 128*n
        counter_cases += 1
    packet = build()
    final_source, final_out = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(final_source)
    record = ledger(packet)
    assert record['polynomial']['operations'] == 524
    assert (record['polynomial']['multiplications'], record['polynomial']['additions_subtractions']) == (318, 206)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_U9_TAG_CHAIN',
        ordinary_clockwise_binary=machine, cts=summary, tag_counts=counts,
        fixed_recipe=recipe, addition_chain=chain, exponent=D,
        independent_modular_power_cases=powers, independent_modular_node_checks=powers*len(chain),
        actual_production_letter_checks=letter_checks,
        full_modular_source_identities=identities, signed_cases=signed,
        exact_counter_bound_cases=counter_cases, ledgers=records,
        source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
        example=dict(source=encoded, output=final_out, comparisons=packet['comparisons'],
                     parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                     fixed_numeral_definitions=compiler.NUMERALS),
        scope='One fixed U9-derived universal polynomial with four positive program parameters, '
              'ordinary positive input, 69 positive witnesses and 524 paid operations. '
              'The genuine machine slice has at least six A symbols; arbitrary singleton '
              'bi-tag inputs are excluded. Degree upper bound only; no expanded universal '
              'production, giant numeral or complete numerical Pell zero is constructed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['ledgers'][-1])
