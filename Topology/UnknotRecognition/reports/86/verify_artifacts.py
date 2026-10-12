#!/usr/bin/env python3
"""Replay representative saved certificates with discovery producers disabled."""
from contextlib import ExitStack
import json
from pathlib import Path
import sys
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent
FAST = ROOT / 'repro/Topology/UnknotRecognition/fast'
EDGE = ROOT / 'artifacts/edge_discovery'
INTERFACE = ROOT / 'artifacts/parallelity'
sys.path[:0] = [str(FAST), str(EDGE), str(INTERFACE)]

from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from parallelity_boundary_verify import verify_parallelity_boundary_interface
from vertex_gate import verify_vertex_disc_certificate


def read(path):
    return json.loads(path.read_text())


def main():
    checks = []
    with ExitStack() as stack:
        for target in [
            'fastunknot.normal_disk_kernel.normal_compressing_disk_count',
            'fastunknot.normal_weight_defect.one_edge_defect_search',
            'fastunknot.normal_weight_defect.weight_defect_search',
            'fastunknot.normal_parallelity.normal_cut_parallelity',
            'parallelity_boundary.parallelity_boundary_interface',
            'vertex_gate.produce_vertex_disc_certificate',
            'vertex_gate._find_rank_minor',
        ]:
            stack.enter_context(patch(target, side_effect=AssertionError(
                'A discovery producer was called during certificate replay')))
        base = read(EDGE / 'vertex-gate-r0.json')
        witness = read(EDGE / 'first-witness.json')
        checks.append(('47-piece native disc certificate',
            verify_normal_disk_count_certificate(base['triangulation'],
                witness['coordinates'], witness['certificate'])))
        for name in ['vertex-gate-r0.json', 'vertex-gate-r64.json']:
            packet = read(EDGE / name)
            checks.append((name, verify_vertex_disc_certificate(
                packet['triangulation'], packet['coordinates'], packet['certificate'])))
        for name in ['full_circle.json', 'partial_collar.json']:
            packet = read(INTERFACE / 'results' / name)
            source = packet['source_parallelity_certificate']
            authenticated = verify_normal_cut_parallelity(packet['triangulation'],
                packet['coordinates'], source)
            checks.append((name + ': source geometry', authenticated))
            checks.append((name + ': boundary interface', authenticated and
                verify_parallelity_boundary_interface(source['geometry'],
                    packet['boundary_certificate'])))
    for name, passed in checks:
        print(('PASS' if passed else 'FAIL') + '  ' + name)
    if not all(passed for _, passed in checks):
        raise SystemExit(1)
    print('All seven representative certificate checks passed; producers disabled.')


if __name__ == '__main__':
    main()
