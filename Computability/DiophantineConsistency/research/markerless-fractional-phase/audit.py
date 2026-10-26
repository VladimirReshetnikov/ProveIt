#!/usr/bin/env python3
"""Exact local Start-mask audit; no whole-cell alignment theorem is claimed."""

import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'padding-staircase-independent'
PROOF_SHA = '69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8'
COEFFICIENT_SHA = '43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93'
RHO = 1 << 47
M = 1 << 45
MASK = M - 4
START = (253, 76, 252, 510)


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(data):
    return (json.dumps(data, indent=2, sort_keys=True) + '\n').encode()


def run():
    require(sha((PARENT / 'PROOF.md').read_bytes()) == PROOF_SHA,
            'Exact complete parent ordinary proof')
    raw = (PARENT / 'coefficients.json').read_bytes()
    require(sha(raw) == COEFFICIENT_SHA, 'Exact whole doubled coefficient array')
    c = json.loads(raw)
    require(len(c) == 3297 and all(type(x) is int and x >= 0 for x in c),
            'Entire coefficient array is literal nonnegative integer data')
    packed = START[0] + (START[1] << 8) + (START[2] << 17) + (START[3] << 25)
    require(c[0] == 2 + 2048 * ((1 << 34) - packed),
            'Actual Start selector coefficient agrees with all four calibrated complemented colors')
    require(MASK == sum(1 << i for i in range(2, 45)), 'Exact 43-bit clause mask')
    require(M == 2048 * (1 << 34), 'Exact mask period for the copied-label word')

    # Enumerate ALL accepted local labels without first assuming label recovery.
    # The mask accepts exactly residue 0..3 modulo M. For a fixed phase,
    # carry, two independent bare/spatial Boolean units and temporal bit,
    # a label W in [0,2^34) is unique for each such residue, if it exists.
    phase_rows = []
    for phase in range(47):
        accepted = []
        for carry in range(58):
            for bare in (0, 1):
                for spatial in (0, 1):
                    for temporal in (0, 1):
                        small = carry + bare + spatial + (temporal << phase)
                        for residue in range(4):
                            numerator = (residue - c[0] - small) % M
                            if numerator % 2048:
                                continue
                            word = numerator // 2048
                            require(0 <= word < 1 << 34, 'Unique complete copied-label range')
                            digit = (c[0] + 2048 * word + small) % RHO
                            require(digit & MASK == 0 and digit % M == residue,
                                    'Every enumerated candidate passes the ACTUAL local mask')
                            expected = packed if phase < 11 else (packed - (temporal << (phase - 11))) % (1 << 34)
                            require(word == expected, 'Recovered residue identity follows from direct mask enumeration')
                            south = word >> 25
                            require(south != 0, 'Every actual accepted local Start mask retains a nonzero South block')
                            if phase <= 10:
                                require(2 + carry + bare + spatial + (temporal << phase) < 2048,
                                        'No unaccounted low-subtotal carry')
                            accepted.append([carry, bare, spatial, temporal, residue, word, south])
        require(accepted, 'Each phase has at least one accepted local configuration before copy tests')
        phase_rows.append({'phase': phase, 'accepted_count': len(accepted),
                           'accepted_sha256': sha(encoded(accepted)),
                           'south_values': sorted({row[-1] for row in accepted}),
                           'full_word_values': sorted({row[-2] for row in accepted})})

    # Independent interval route: demand South=0 outright, allowing ALL lower
    # 25 copied bits. Solve the mask congruence without using the identity above.
    zero_south_survivors = []
    for phase in range(47):
        for carry in range(58):
            for units in range(3):
                for temporal in (0, 1):
                    base = c[0] + carry + units + (temporal << phase)
                    for residue in range(4):
                        numerator = (residue - base) % M
                        if numerator % 2048 == 0 and numerator // 2048 < 1 << 25:
                            zero_south_survivors.append([phase, carry, units, temporal, residue, numerator // 2048])
    require(not zero_south_survivors, 'Direct interval route excludes all zero-South Start labels')

    # Copy parity is a conditional local implication. It requires incoming
    # carry zero, Boolean current South and no other odd non-temporal source.
    parity_rows = []
    for phase in range(1, 47):
        survivors = [south for south in (0, 1) for temporal in (0, 1)
                     for even_background in (0, 2, RHO - 2, RHO, 2 * RHO)
                     if ((south + (temporal << phase) + even_background) % RHO) % 2 == 0]
        require(set(survivors) == {0}, 'Every positive fractional phase forces each reset South copy to zero')
        parity_rows.append({'phase': phase, 'surviving_South_bits': sorted(set(survivors))})

    # Actual marker-deleted geometry at C1005: check the complete reset-band
    # envelopes under the independently stated n<=1 premise. This does not
    # assert or re-prove the preliminary count theorem after redesign.
    support = set(range(951)) | set(range(960, 986))
    center = 1005
    dc = {center - e: value for e, value in enumerate(c) if value}
    dc[18] = dc.get(18, 0) + 1
    reset_rows = []
    for h in range(969):
        terms = [(e, center + e - h, c[center + e - h]) for e in sorted(support)
                 if 0 <= center + e - h < len(c) and c[center + e - h]]
        selector = [value for e, _, value in terms if e < 942]
        controls = [value for e, _, value in terms if e >= 942]
        bound = max(selector, default=0) + sum(controls)
        require(bound + RHO // 2 + 2 + 57 < RHO,
                'All low outgoing carries reset under one-hot and arbitrary Boolean controls')
        reset_rows.append([h, terms, bound])
    copy_rows = []
    for j in range(9):
        h = 960 + j
        hits = [(e, dc[h-e]) for e in sorted(support) if h-e in dc]
        require([(e, v % 2) for e, v in hits if v % 2] == [(942+j, 1)] and h-9 not in support,
                'Entire marker-deleted South-copy odd part and absent spatial predecessor')
        copy_rows.append([h, hits])

    # Explicit unresolved alignment cases: all eight forced Start ones have
    # available temporal predecessors at offsets1 and18 as well as0.
    offsets = [r for r in (0, 1, 18)
               if all(h-r in support for h in range(961, 969))]
    require(offsets == [0, 1, 18], 'Marker deletion leaves genuine geometry cases outside fractional-phase exclusion')
    require([h-18 for h in range(960, 969)] == list(range(942, 951)),
            'Offset18 sends every North copy to the physical South family')
    require(any(((1 + 1 + (temporal << phase)) % RHO) % 2 == 0
                for phase in range(1, 47) for temporal in (0, 1)),
            'Negative control: incoming carry1 destroys the zero-South parity implication')

    return {'schema': 'markerless_fractional_phase_conditional_v1',
            'script_sha256': sha(Path(__file__).read_bytes()),
            'parent_proof_sha256': PROOF_SHA, 'coefficient_sha256': COEFFICIENT_SHA,
            'Start_complement': list(START), 'Start_packed': packed, 'Start_coefficient': c[0],
            'all47_local_masks': phase_rows, 'all46_positive_phase_parities': parity_rows,
            'zero_South_direct_interval_survivors': zero_south_survivors,
            'marker_deleted_support_size': len(support),
            'conditional_reset_geometry': {'count': len(reset_rows), 'sha256': sha(encoded(reset_rows)),
                                           'maximum': max(row[2] for row in reset_rows)},
            'complete_copy_geometry': {'count': len(copy_rows), 'sha256': sha(encoded(copy_rows))},
            'unresolved_whole_field_offsets': offsets[1:],
            'scope': 'Conditional local fractional-phase exclusion after one-hot and low carry resets. No complete markerless native theorem, controller, ports, equation or whole-cell alignment claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    raw = encoded(run())
    path = HERE / 'RESULTS.json'
    if args.write:
        path.write_bytes(raw)
    else:
        require(path.read_bytes() == raw, 'Exact deterministic finite receipt')
    print(json.dumps({'status': 'PASS', 'script_sha256': sha(Path(__file__).read_bytes()),
                      'receipt_sha256': sha(raw)}, sort_keys=True))


if __name__ == '__main__':
    main()
