"""Tiny native connected-sum fixture audit; run with fast/ on PYTHONPATH.

No exterior construction, LP, normal-surface enumeration, or oracle is used.
Every factor is identified by an explicit slot-preserving PD edge bijection,
which is stronger than comparing a knot polynomial or crossing count.
"""
from hashlib import sha256
import json
from pathlib import Path

from fastunknot import diagram as diagram_module
from fastunknot import interlace as interlace_module
from fastunknot.diagram import Diagram
from fastunknot.interlace import (
    visible_factors_interlacement,
    verify_interlacement_certificate,
)


BASES = {
    'T': (2, [1, 1, 1]),
    'F': (3, [1, -2, 1, -2]),
}
CASES = {
    'tt': (3, [1, 1, 1, 2, 2, 2], ['T', 'T']),
    'tf': (4, [1, 1, 1, 2, -3, 2, -3], ['T', 'F']),
    'ff': (5, [1, -2, 1, -2, 3, -4, 3, -4], ['F', 'F']),
}


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def pins():
    return {
        module.__name__: sha256(Path(module.__file__).read_bytes()).hexdigest()
        for module in (diagram_module, interlace_module)
    }


def slot_preserving_edge_map(base, factor):
    assert base.crossings == factor.crossings
    forward, backward = {}, {}
    for base_row, factor_row in zip(base.pd, factor.pd):
        for a, b in zip(base_row, factor_row):
            assert forward.setdefault(a, b) == b
            assert backward.setdefault(b, a) == a
    assert set(forward) == set(range(2 * base.crossings))
    assert set(backward) == set(range(2 * factor.crossings))
    # Preserve the rotation system and under/over slots exactly. In
    # particular this does not identify a trefoil with its mirror.
    assert tuple(tuple(forward[x] for x in row) for row in base.pd) == factor.pd
    return [forward[x] for x in range(2 * base.crossings)]


def main():
    start_pins = pins()
    bases = {name: Diagram.from_braid(n, word) for name, (n, word) in BASES.items()}
    records = []
    for name, (strands, word, expected) in CASES.items():
        original = Diagram.from_braid(strands, word)
        # Independently exercise bare-PD validation, losing auxiliary braid
        # provenance before factor discovery and combinatorial verification.
        diagram = Diagram.from_pd(original.pd)
        factors, certificate = visible_factors_interlacement(diagram)
        gauss_word = [dart // 4 for dart in diagram.traversal()]
        assert verify_interlacement_certificate(gauss_word, certificate)
        assert len(factors) == len(expected)
        assert sum(f.crossings for f in factors) == diagram.crossings
        checks = []
        for factor, base_name in zip(factors, expected):
            base = bases[base_name]
            mapping = slot_preserving_edge_map(base, factor)
            checks.append(dict(
                base=base_name, factor_pd=factor.pd, base_pd=base.pd,
                base_edge_to_factor_edge=mapping,
                crossing_permutation=list(range(base.crossings)),
                slot_rotations=[0] * base.crossings,
                reflection_used=False, factor_pd_sha256=digest(factor.pd),
            ))
        records.append(dict(
            id=name, braid=dict(strands=strands, word=word),
            pd=diagram.pd, pd_sha256=digest(diagram.pd),
            gauss_word=gauss_word, factor_certificate=certificate,
            native_interlacement_verified=True, factors=checks,
        ))
        print(name, certificate['crossing_components'],
              [x['base_edge_to_factor_edge'] for x in checks])
    assert pins() == start_pins
    output = dict(passed=True, source_sha256=start_pins,
                  scope='Exact visible diagram factors; no claim about normal cones, extrema, Euler transport, or resolving-number growth.',
                  records=records)
    path = Path(__file__).with_name('fixtures.json')
    path.write_text(json.dumps(output, indent=2) + '\n')
    print(path)


if __name__ == '__main__':
    main()
