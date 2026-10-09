"""Write a small pruning certificate and a complete checked assembly example."""
from __future__ import annotations
import json
from pathlib import Path
from disk_kernel import Candidate, reduce_family, partitions, minimum_completion
from certificate_check import verify_certificate
from assembly import solve, replay_surface
from benchmark import instance

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    items = [Candidate((0, 0, 1), 0), Candidate((0, 1, 0), 0), Candidate((0, 1, 1), 1)]
    reduced = reduce_family(items)
    assert verify_certificate([x.partition for x in items], [x.cost for x in items], reduced.certificate)
    queries = []
    for q in partitions(3):
        x = minimum_completion(items, q)
        y = minimum_completion(reduced.retained, q)
        assert (None if x is None else x.cost) == (None if y is None else y.cost)
        queries.append({'cap': list(q), 'original_optimum': None if x is None else x.cost,
                        'reduced_optimum': None if y is None else y.cost})
    local = {'scope': 'abstract disk completion, not arbitrary guards',
             'partitions': [list(x.partition) for x in items], 'costs': [x.cost for x in items],
             'certificate': reduced.certificate, 'queries': queries,
             'same_component_guard_preserved': False}
    initial, layers, caps = instance(4)
    result = solve(initial, layers, caps, collect_certificates=True)
    baseline = solve(initial, layers, caps, compressed=False)
    assert (result['status'], result['cost']) == (baseline['status'], baseline['cost'])
    for e in result['certificates']:
        assert verify_certificate(e['partitions'], e['costs'], e['certificate'])
    replay = replay_surface(initial, layers, caps, result['witness'])
    assert replay['is_disk'] and replay['cost'] == result['cost']
    def candidate(c):
        return {'partition': list(c.partition), 'cost': c.cost}
    assembly = {
        'schema': 'abstract_arc_assembly_v1',
        'scope': 'abstract PL surface; no ambient embedding or knot certificate',
        'initial': [candidate(x) for x in initial],
        'layers': [{'input_width': z.input_width, 'output_width': z.output_width,
                    'options': [candidate(x) for x in z.options]} for z in layers],
        'caps': [candidate(x) for x in caps],
        'reduced_result': result,
        'exact_result_without_certificates': baseline,
        'independent_surface_replay': replay,
    }
    (ROOT / 'examples').mkdir(exist_ok=True)
    (ROOT / 'examples/small_reduction.json').write_text(json.dumps(local, indent=2) + '\n')
    (ROOT / 'examples/complete_assembly.json').write_text(json.dumps(assembly, indent=2) + '\n')
    print(json.dumps({'local_rows': len(items), 'retained_rows': len(reduced.retained),
                      'all_caps_checked': len(queries), 'assembly_status': result['status'],
                      'assembly_cost': result['cost'], 'literal_replay': replay}, indent=2))

if __name__ == '__main__':
    main()
