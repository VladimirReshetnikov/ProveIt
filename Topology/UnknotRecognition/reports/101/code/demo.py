"""Construct a source-bound flag proof; no knot-recognition verdict is issued.

Examples:
  python -B code/demo.py --mode solid-torus
  python -B code/demo.py --mode periodic --bits 128 --output examples/periodic_128.json
  python -B code/demo.py --mode convex --copies 1 --output examples/convex_cone.json
"""
from __future__ import annotations
import argparse
from pathlib import Path
from atlas import canonical_data, digest, dumps, simplex
from flags import compile_flags, certificate_data, inventory
from replay import verify
from sources import tetrahedral_atlas, solid_torus_source, polytope_ball, product_with_line


def example(mode: str, bits: int = 128, copies: int = 1) -> dict:
    if mode == 'solid-torus':
        source_spec = {'tetrahedra': solid_torus_source(), 'normal_coordinates': [[0]*7]}
        source, metadata = tetrahedral_atlas(source_spec['tetrahedra'])
        parameters = {}
    elif mode == 'periodic':
        if not 1 <= bits <= 16384:
            raise ValueError('bits must be between 1 and 16384')
        source_spec = {'kind': 'triangle-times-periodic-line', 'segments': (1 << bits)+1}
        source = product_with_line(polytope_ball(simplex(2)), source_spec['segments'], True)
        parameters = {'bits': bits}
    elif mode == 'convex':
        if type(copies) is not int or not 1 <= copies <= 1000000:
            raise ValueError('copies must be between 1 and 1000000')
        source_spec = {'kind': 'disjoint-convex-tetrahedra', 'copies': copies}
        source = polytope_ball(simplex(3), copies)
        parameters = {'copies': copies}
    else:
        raise ValueError('unknown mode')
    certificate = compile_flags(source)
    if not verify(source, certificate):
        raise RuntimeError('independent flag replay failed')
    result = {
        'schema': 'source-bound-flag-example-v1', 'mode': mode, 'parameters': parameters,
        'source_specification': source_spec, 'source_atlas': canonical_data(source),
        'certificate': certificate_data(certificate), 'source_sha256': digest(source),
        'inventory': inventory(certificate.result),
        'scope': 'Regularized source representation; not an unknot or knotted verdict.'
    }
    if mode == 'solid-torus':
        from reference import expanded_cells, homology, compare_source_oracle
        result['literal_source_comparison'] = compare_source_oracle(source_spec['tetrahedra'], metadata, certificate)
        cells, facets, all_faces, marks = expanded_cells(certificate.result)
        result['homology_F2'] = homology(cells, facets, 2)
        result['homology_F3'] = homology(cells, facets, 3)
        result['boundary_homology_F2'] = homology(cells, facets, 2, marks['boundary'])
    if mode == 'convex':
        from morse_adapter import convex_cone_certificate, rm
        packet, proof, critical = convex_cone_certificate(simplex(3), copies, source, certificate)
        # Store the predecessor's own wire format as a string. Its large-integer
        # tag is intentionally distinct from the atlas format's $hex tag.
        result['morse_certificate_json'] = rm.dumps_certificate(packet, proof)
        result['critical_cells'] = critical
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--mode', choices=('solid-torus', 'periodic', 'convex'), default='solid-torus')
    parser.add_argument('--bits', type=int, default=128)
    parser.add_argument('--copies', type=int, default=1)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        result = example(args.mode, args.bits, args.copies)
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(dumps(result)+'\n', encoding='utf-8')
        summary = {k: result[k] for k in ('mode', 'parameters', 'source_sha256', 'inventory', 'scope')}
        if 'critical_cells' in result: summary['critical_cells'] = result['critical_cells']
        if 'homology_F2' in result: summary['homology_F2'] = result['homology_F2']
        if args.output: summary['output'] = str(args.output)
        print(dumps(summary))
        return 0
    except (ValueError, OSError, RuntimeError) as exc:
        parser.exit(1, f'error: {exc}\n')

if __name__ == '__main__':
    raise SystemExit(main())
