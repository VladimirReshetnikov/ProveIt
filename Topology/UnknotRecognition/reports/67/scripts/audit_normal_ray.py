"""Replay primitive-ray disc certificates against the frozen Regina corpus."""
import argparse
import copy
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'work' / 'fast' if (ROOT / 'work').exists() else ROOT / 'fast'))
from fastunknot.normal_ray import certify_normal_ray_disc
from fastunknot.normal_ray_verify import verify_normal_ray_disc


def run(output):
    corpus = json.loads((ROOT / 'results/discovery_corpus.json').read_text())
    records, positives, mutations = [], [], 0
    for fixture in corpus['records']:
        raw = fixture['triangulation']
        for index, vertex in enumerate(fixture['standard_vertices']):
            rows = vertex['coordinates']
            answer = certify_normal_ray_disc(raw, rows)
            expected = vertex['essential_disc']
            success = answer['status'] == 'DISC_FOUND'
            if success != expected:
                raise AssertionError((fixture['id'], index, expected, answer))
            if success:
                proof = answer['certificate']
                assert verify_normal_ray_disc(raw, rows, proof)
                positives.append(dict(fixture_id=fixture['id'], vertex_index=index,
                                      certificate=proof))
                for key, bad in [('prime', 65520), ('rank_rows', []),
                                 ('input_sha256', '0'*64),
                                 ('boundary_homology', {'nonzero': False, 'vertex_values': []})]:
                    altered = copy.deepcopy(proof)
                    altered[key] = bad
                    assert not verify_normal_ray_disc(raw, rows, altered)
                    mutations += 1
                twice = [[2*x for x in row] for row in rows]
                assert not verify_normal_ray_disc(raw, twice, proof)
                mutations += 1
            records.append(dict(fixture_id=fixture['id'], vertex_index=index,
                                expected=expected, status=answer['status']))
    # The verifier remains usable with every producer entry point disabled.
    import fastunknot.normal_ray as producer
    saved = producer.certify_normal_ray_disc
    def forbidden(*args, **kwargs):
        raise AssertionError('producer invoked during independent replay')
    producer.certify_normal_ray_disc = forbidden
    fixtures = {f['id']: f for f in corpus['records']}
    try:
        for record in positives:
            fixture = fixtures[record['fixture_id']]
            rows = fixture['standard_vertices'][record['vertex_index']]['coordinates']
            assert verify_normal_ray_disc(fixture['triangulation'], rows, record['certificate'])
    finally:
        producer.certify_normal_ray_disc = saved
    result = dict(schema='normal-ray-audit-v1', fixtures=len(fixtures),
                  exact_comparisons=len(records), positive_replays=len(positives),
                  independent_replays=len(positives), mutation_rejections=mutations,
                  records=records, certificates=positives)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('fixtures', 'exact_comparisons',
                     'positive_replays', 'independent_replays', 'mutation_rejections')}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT/'results/reproduced/ray_audit.json')
    run(parser.parse_args().output)
