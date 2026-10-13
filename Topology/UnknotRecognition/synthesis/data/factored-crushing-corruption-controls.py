"""Replay one retained genuine UU result and reject 19 saved-result mutations.

Run from any directory. No recognition, factor, LP or crushing producer is used.
This is a proof/accounting corruption control, not a timing measurement.
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
from factored_crushing_research.check_evidence import replay_result
from factored_crushing_research.common import configs, source_hashes


def main():
    if not __debug__:
        raise RuntimeError('corruption replay requires assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', type=Path, default=DATA/'factored-crushing-corruption-fixture.json')
    parser.add_argument('--output', type=Path, default=DATA/'factored-crushing-corruption-controls.json')
    args = parser.parse_args()
    raw = args.fixture.read_bytes()
    fixture = json.loads(raw)
    pins = source_hashes()
    assert fixture['schema'] == 'factored-crushing-corruption-fixture-v1'
    assert fixture['source_sha256'] == pins and fixture['config'] == configs()
    diagram = Diagram.from_pd(fixture['input_pd'])
    assert diagram == Diagram.from_braid(3, [1, 2])
    original = fixture['result']
    assert replay_result(diagram, 'factored', original, fixture['config'])
    mutations = [
        ('bool total', lambda x: x['stats'].update(factors_total=True)),
        ('missing factor', lambda x: x['factor_results'].pop()),
        ('out of order', lambda x: x['factor_results'].reverse()),
        ('duplicate index', lambda x: x['factor_results'][1].update(factor_index=0)),
        ('bool index', lambda x: x['factor_results'][0].update(factor_index=False)),
        ('wrong factor PD', lambda x: x['factor_pds'].__setitem__(1, [])),
        ('forged whole status', lambda x: x.update(status='KNOTTED')),
        ('missing cap counter', lambda x: x['factor_results'][0]['result']['stats'].pop('anchors_tested')),
        ('negative child stat', lambda x: x['factor_results'][0]['result']['stats'].update(anchors_tested=-1)),
        ('bool child stat', lambda x: x['factor_results'][0]['result']['stats'].update(anchors_tested=False)),
        ('float child stat', lambda x: x['factor_results'][0]['result']['stats'].update(anchors_tested=0.0)),
        ('exceeded child cap', lambda x: x['factor_results'][0]['result']['stats'].update(anchors_tested=10001)),
        ('inconsistent aggregate', lambda x: x['stats'].update(anchors_tested=1)),
        ('incorrect peak', lambda x: x['stats'].update(maximum_tableau_bits=99)),
        ('bad child source', lambda x: x['factor_results'][0]['result']['certificate']['chain'].update(input_pd=[])),
        ('bad child steps', lambda x: x['factor_results'][0]['result']['certificate']['chain']['steps'].clear()),
        ('missing quorum', lambda x: x['certificate']['proofs'].pop()),
        ('noncanonical proof order', lambda x: x['certificate']['proofs'].reverse()),
        ('forged factor partition', lambda x: x['factorization'].update(crossing_components=[[0, 1]])),
    ]
    records = []
    for name, mutate in mutations:
        changed = deepcopy(original)
        mutate(changed)
        try:
            replay_result(diagram, 'factored', changed, fixture['config'])
        except (AssertionError, KeyError, ValueError, TypeError, IndexError):
            records.append(dict(name=name, rejected=True))
        else:
            raise AssertionError('accepted mutation: '+name)
    assert len(records) == 19 and source_hashes() == pins
    output = dict(passed=True, valid_control=True, rejected_mutations=19,
        scope='Genuine retained two-curl result replay and saved-result corruption controls; no discovery or timing.',
        source_sha256=pins, fixture_sha256=sha256(raw).hexdigest(),
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), records=records)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(dict(passed=True, valid_control=True, rejected_mutations=19), sort_keys=True))


if __name__ == '__main__':
    main()
