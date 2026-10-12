"""Replay a saved finite algebraic packet without invoking either producer.

The geometric input hypotheses are deliberately not authenticated here.
Untrusted packets are capped in file size and in Smith replay resources.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from interface_homology import Core, Loop, Surface, Model, Condensation, unwire, wire
from interface_homology.replay import verify_condensation
from interface_homology.smith import SmithCertificate, verify_smith, torsion_blocks


def decode_model(data: dict) -> Model:
    if set(data) != {'core', 'surfaces'}:
        raise ValueError('unexpected model keys')
    c = dict(data['core'])
    c['edges'] = tuple(tuple(e) for e in c['edges'])
    c['faces'] = tuple(Loop(anchor=x['anchor'], word=tuple(x['word'])) for x in c['faces'])
    surfaces = []
    for raw in data['surfaces']:
        s = dict(raw)
        s['circles'] = tuple(Loop(anchor=x['anchor'], word=tuple(x['word'])) for x in s['circles'])
        s['intervals'] = tuple(s['intervals'])
        surfaces.append(Surface(**s))
    return Model(Core(**c), tuple(surfaces))


def replay(path: Path) -> dict:
    if path.stat().st_size > 1_048_576:
        raise ValueError('saved finite example exceeds 1 MiB replay allowance')
    raw = unwire(json.loads(path.read_text()))
    if raw.get('schema') != 'saved-algebraic-interface-example-v1':
        raise ValueError('unknown saved-example schema')
    model = decode_model(raw['model'])
    # This command is an intentionally finite example replayer, not a service.
    # Binary genus/multiplicity values need no expansion, but explicit core
    # dimensions and path lengths must also be capped before allocating arrays.
    if (type(model.core.vertices) is not int or model.core.vertices > 20_000
            or len(model.core.edges) > 5_000 or len(model.core.faces) > 5_000
            or len(model.surfaces) > 5_000):
        raise ValueError('explicit model dimensions exceed replay allowance')
    words = list(model.core.faces) + [c for b in model.surfaces for c in b.circles]
    if sum(len(c.word) for c in words) > 100_000:
        raise ValueError('explicit core words exceed replay allowance')
    p = dict(raw['condensation'])
    p['matrix'] = tuple(tuple(r) for r in p['matrix'])
    for field in ('core_generators', 'core_forest', 'core_component',
                  'saturated_orientable', 'saturated_nonorientable', 'surface_free'):
        p[field] = tuple(p[field])
    packet = Condensation(**p)
    s = dict(raw['smith'])
    s['diagonal'] = tuple(s['diagonal'])
    s['operations'] = tuple(tuple(op) for op in s['operations'])
    normal = SmithCertificate(**s)
    if not verify_condensation(model, packet):
        raise ValueError('independent condensation replay rejected the packet')
    if not verify_smith(packet.matrix, normal, cols=packet.relation_count,
                        max_operations=100_000, max_entry_bits=1_000_000):
        raise ValueError('independent Smith replay rejected the packet')
    return {
        'status': 'VALID_ALGEBRAIC_CERTIFICATE',
        'model_sha256': packet.source_sha256,
        'H0_rank': packet.b0,
        'H1_free_rank': packet.rows - len(normal.diagonal) + packet.free_bulk,
        'H1_torsion_invariant_factor_runs': torsion_blocks(normal.diagonal, packet.two_torsion_bulk),
        'geometric_source_verified': False,
        'S3_embedding_verified': False,
        'knot_verdict': None,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path', nargs='?', type=Path,
                        default=ROOT/'examples'/'mobius_certificate.json')
    args = parser.parse_args()
    try:
        result = replay(args.path)
    except (OSError, ValueError, TypeError, KeyError, IndexError, AttributeError) as exc:
        print(f'REJECTED: {exc}', file=sys.stderr)
        return 1
    print(json.dumps(wire(result), indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
