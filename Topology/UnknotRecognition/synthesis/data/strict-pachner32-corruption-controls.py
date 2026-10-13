"""Replay genuine retained circle results and reject saved-result corruptions.

Run from any directory. No recognition, Pachner, LP or crushing producer is
used. These are proof/accounting controls, not performance measurements.
"""
import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot.diagram import Diagram
from strict_pachner32_research.check_evidence import replay_result
from strict_pachner32_research.common import ARMS, configs, source_hashes


def main():
    if not __debug__:
        raise RuntimeError('corruption replay requires assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', type=Path, default=DATA/'strict-pachner32-corruption-fixture.json')
    parser.add_argument('--output', type=Path, default=DATA/'strict-pachner32-corruption-controls.json')
    args = parser.parse_args()
    raw = args.fixture.read_bytes()
    fixture = json.loads(raw)
    pins = source_hashes()
    assert fixture['schema'] == 'strict-pachner32-corruption-fixture-v1'
    assert fixture['source_sha256'] == pins
    assert fixture['input_pd'] == []
    assert fixture['config'] == {arm: configs(arm) for arm in ARMS}
    diagram = Diagram.from_pd(fixture['input_pd'])
    for arm in ARMS:
        assert replay_result(diagram, arm, fixture['results'][arm], configs(arm))
    original = fixture['results']['pachner32']
    mutations = [
        ('bool move counter', lambda x: x['stats'].update(pachner32_moves=False)),
        ('negative scan counter', lambda x: x['stats'].update(pachner32_calls=-1)),
        ('float candidate counter', lambda x: x['stats'].update(pachner32_candidates=0.0)),
        ('missing move counter', lambda x: x['stats'].pop('pachner32_moves')),
        ('missing scan counter', lambda x: x['stats'].pop('pachner32_calls')),
        ('forged retained move count', lambda x: x['stats'].update(pachner32_moves=1, pachner32_calls=1, pachner32_candidates=1)),
        ('impossible scan count', lambda x: x['stats'].update(pachner32_calls=x['stats']['stages']+1)),
        ('missing cap counter', lambda x: x['stats'].pop('anchors_tested')),
        ('exceeded node cap', lambda x: x['stats'].update(nodes_attempted=257)),
        ('exceeded anchor cap', lambda x: x['stats'].update(anchors_tested=10001)),
        ('negative pivot counter', lambda x: x['stats'].update(lp_pivots=-1)),
        ('float anchor counter', lambda x: x['stats'].update(anchors_tested=0.0)),
        ('unrecognized peak counter', lambda x: x['stats'].update(maximum_unrecognized=1)),
        ('wrong initial size', lambda x: x['stats'].update(initial_tetrahedra=1)),
        ('wrong shelled size', lambda x: x['stats'].update(shelled_tetrahedra=1)),
        ('wrong stage count', lambda x: x['stats'].update(stages=0)),
        ('wrong crushing count', lambda x: x['stats'].update(crushing_steps=0)),
        ('wrong unlayering count', lambda x: x['stats'].update(boundary_unlayerings=1)),
        ('forged whole verdict', lambda x: x.update(status='KNOTTED')),
        ('deleted terminal proof', lambda x: x['certificate']['chain']['steps'].clear()),
        ('wrong original PD', lambda x: x['certificate']['chain'].update(input_pd=[[1, 1, 0, 0]])),
        ('empty source tetrahedra', lambda x: x['certificate']['chain']['source_triangulation'].update(tetrahedra=[])),
        ('legacy chain option mismatch', lambda x: x['certificate']['chain'].update(schema='diagram-crushing-v2')),
        ('false terminal successor', lambda x: x['certificate']['chain'].update(triangulation={'tetrahedra': []})),
        ('tampered step source binding', lambda x: x['certificate']['chain']['steps'][0].update(source_sha256='0'*64)),
    ]
    records = []
    def reject(name, arm, value, options):
        try:
            replay_result(diagram, arm, value, options)
        except (AssertionError, KeyError, ValueError, TypeError, IndexError):
            records.append(dict(name=name, rejected=True))
        else:
            raise AssertionError('accepted mutation: '+name)
    for name, mutate in mutations:
        changed = deepcopy(original)
        mutate(changed)
        reject(name, 'pachner32', changed, configs('pachner32'))
    changed = deepcopy(fixture['results']['baseline'])
    changed['stats'].update(pachner32_moves=0)
    reject('disabled option added move statistics', 'baseline', changed, configs('baseline'))
    wrong_options = configs('pachner32')
    wrong_options['reduce_pachner32'] = False
    reject('wrong option binding', 'pachner32', original, wrong_options)
    assert len(records) == 27 and source_hashes() == pins
    output = dict(passed=True, valid_control=True, rejected_mutations=len(records),
        scope='Both genuine retained circle results plus proof and recorded-counter corruptions; no discovery or timing.',
        source_sha256=pins, fixture_sha256=sha256(raw).hexdigest(),
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), records=records)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(dict(passed=True, valid_control=True, rejected_mutations=len(records)), sort_keys=True))


if __name__ == '__main__':
    main()
