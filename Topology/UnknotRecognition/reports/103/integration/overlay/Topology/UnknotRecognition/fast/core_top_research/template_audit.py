"""Retain universal-template and binary-scale evidence on genuine source cuts."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import sys

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.core_top_template import (
    compile_source_top_tree, specialize_source_top_tree, verify_source_top_tree,
)
from fastunknot.core_top_reduction_verify import replay_core_top_reduction
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.integer_codec import json_safe
from normal_orbit_research.fixtures import interior_vertex_torus


def digest(value):
    return hashlib.sha256(json.dumps(json_safe(value), sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw, basis = interior_vertex_torus()
    template = compile_source_top_tree(raw)
    assert verify_source_top_tree(raw, template)
    records = []
    choices = Counter()
    for coefficients in product(range(4), repeat=3):
        rows = [[sum(c*basis[name][t][j] for c, name in
                     zip(coefficients, ('sphere', 'boundary_disk', 'mobius')))
                 for j in range(7)] for t in range(len(raw['tetrahedra']))]
        geometry = normal_cut_parallelity(raw, rows)['geometry']
        proof = specialize_source_top_tree(raw, rows, geometry, template)
        reduced = replay_core_top_reduction(raw, rows, geometry, proof)
        assert reduced is not None and not reduced['core']['handles3']
        assert reduced['ports'] == geometry['ports']
        choices[str(proof['moves'])] += 1
        records.append(dict(coefficients=coefficients, normal_coordinates=rows,
                            source_geometry_sha256=digest(geometry),
                            top_certificate=proof, independent_replay=True))
    scales = []
    for exponent in (0, 64, 16384):
        rows = [[(1 << exponent)*n for n in row] for row in basis['boundary_disk']]
        geometry = normal_cut_parallelity(raw, rows)['geometry']
        proof = specialize_source_top_tree(raw, rows, geometry, template)
        assert replay_core_top_reduction(raw, rows, geometry, proof) is not None
        scales.append(dict(scale_power_of_two=exponent,
            maximum_coordinate_bits=max(n.bit_length() for row in rows for n in row),
            certificate_bytes=len(json.dumps(json_safe(proof), sort_keys=True).encode()),
            top_certificate=proof, independent_replay=True))
    assert len({s['certificate_bytes'] for s in scales}) == 1
    report = dict(scope='fixed source universal top-tree specialization; no hierarchy bound',
        python=platform.python_version(), triangulation=raw, source_sha256=digest(raw),
        template=template, independently_verified_template=True,
        compatible_vectors=len(records), basis_names=['sphere', 'boundary_disk', 'mobius'],
        specialized_move_choices=dict(choices), cases=records, binary_scale_cases=scales,
        source_hashes={name: hashlib.sha256((FAST/name).read_bytes()).hexdigest()
            for name in ('fastunknot/core_top_template.py',
                         'fastunknot/core_top_reduction.py',
                         'fastunknot/core_top_reduction_verify.py',
                         'core_top_research/template_audit.py')})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    print(json.dumps(dict(compatible_vectors=len(records), choices=len(choices),
                         scales=[{k:v for k,v in s.items() if k != 'top_certificate'}
                                 for s in scales])))


if __name__ == '__main__':
    main()
