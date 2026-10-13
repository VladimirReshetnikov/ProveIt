"""Saved proof/accounting/binding corruption controls; no discovery or timing.

The fixture refers to the complete audit by exact relative path and byte hash.
The native-valid endpoint challenge demonstrates why native recognition replay
alone cannot establish equality to a separate source-specific h experiment.
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
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.normal_pachner_descent_verify import verify_normal_pachner_descent
from pachner_descent_research.check_evidence import check_audit, replay_result
from pachner_descent_research.common import ARMS, configs, source_hashes
from pachner_descent_endpoint_binding import check_endpoint_bindings


def macro_of(result):
    chain = result['certificate']['chain']
    source = chain['source_triangulation'] if chain['shelling'] is None else chain['shelling']['triangulation']
    for step in chain['steps']:
        if step['schema'] == 'normal-pachner-descent-v1':
            return source, step
        source = step['successor']
    raise AssertionError('missing genuine macro control')


def main():
    assert __debug__, 'corruption controls require assertions enabled'
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', type=Path, default=DATA/'pachner-descent-corruption-fixture.json')
    parser.add_argument('--output', type=Path, default=DATA/'pachner-descent-corruption-controls.json')
    args = parser.parse_args()
    raw = args.fixture.read_bytes()
    fixture = json.loads(raw)
    pins = source_hashes()
    assert fixture['schema'] == 'pachner-descent-corruption-fixture-v1'
    assert fixture['source_sha256'] == pins
    audit_path = Path(fixture['audit_file'])
    assert not audit_path.is_absolute() and audit_path.name == str(audit_path)
    audit_bytes = (DATA/audit_path).read_bytes()
    assert sha256(audit_bytes).hexdigest() == fixture['audit_sha256']
    audit = json.loads(audit_bytes)
    assert audit['passed'] is True and check_endpoint_bindings(audit)['endpoint_bindings'] == 12
    circle = audit['records'][0]
    assert circle['id'] == 'circle' and circle['input_pd'] == []
    diagram = Diagram.from_pd([])
    for arm in ARMS:
        replay_result(diagram, arm, circle['arms'][arm]['result'], configs(arm))
    original = circle['arms']['u1']['result']
    records = []
    def reject(name, verify):
        try:
            accepted = verify()
        except (AssertionError, KeyError, ValueError, TypeError, IndexError):
            accepted = False
        assert not accepted, 'accepted mutation: '+name
        records.append(dict(name=name, rejected=True))
    mutations = [
        ('bool macro counter', lambda x: x['stats'].update(pachner_descent_macros=False)),
        ('negative descent search counter', lambda x: x['stats'].update(pachner_descent_calls=-1)),
        ('float descent work counter', lambda x: x['stats'].update(pachner_descent_work=0.0)),
        ('missing descent node counter', lambda x: x['stats'].pop('pachner_descent_nodes')),
        ('missing macro counter', lambda x: x['stats'].pop('pachner_descent_macros')),
        ('unknown descent statistic', lambda x: x['stats'].update(pachner_descent_unrecognized=0)),
        ('impossible descent search count', lambda x: x['stats'].update(pachner_descent_calls=x['stats']['stages']+1)),
        ('forged retained macro count', lambda x: x['stats'].update(pachner_descent_macros=1,pachner_descent_calls=1,pachner_descent_downward_moves=1)),
        ('forged elementary up count', lambda x: x['stats'].update(pachner_descent_upward_moves=1)),
        ('forged elementary down count', lambda x: x['stats'].update(pachner_descent_downward_moves=1)),
        ('missing anchor cap counter', lambda x: x['stats'].pop('anchors_tested')),
        ('exceeded node cap', lambda x: x['stats'].update(nodes_attempted=257)),
        ('exceeded anchor cap', lambda x: x['stats'].update(anchors_tested=10001)),
        ('exceeded ellipsoid cap', lambda x: x['stats'].update(lp_ellipsoid_iterations=10001)),
        ('negative pivot counter', lambda x: x['stats'].update(lp_pivots=-1)),
        ('unrecognized peak counter', lambda x: x['stats'].update(maximum_unrecognized=1)),
        ('wrong initial size', lambda x: x['stats'].update(initial_tetrahedra=1)),
        ('wrong stage count', lambda x: x['stats'].update(stages=0)),
        ('wrong crushing count', lambda x: x['stats'].update(crushing_steps=0)),
        ('forged whole verdict', lambda x: x.update(status='KNOTTED')),
        ('deleted terminal proof', lambda x: x['certificate']['chain']['steps'].clear()),
        ('wrong original PD', lambda x: x['certificate']['chain'].update(input_pd=[[1,1,0,0]])),
        ('legacy chain option mismatch', lambda x: x['certificate']['chain'].update(schema='diagram-crushing-v3')),
    ]
    for name, mutate in mutations:
        changed = deepcopy(original)
        mutate(changed)
        reject(name, lambda changed=changed: replay_result(diagram, 'u1', changed, configs('u1')))
    changed = deepcopy(circle['arms']['baseline']['result'])
    changed['stats']['pachner_descent_macros'] = 0
    reject('disabled option added macro stats', lambda: replay_result(diagram, 'baseline', changed, configs('baseline')))
    wrong_options = configs('u1')
    wrong_options['reduce_pachner_descent'] = False
    reject('wrong whole option binding', lambda: replay_result(diagram, 'u1', original, wrong_options))

    trefoil = next(r for r in audit['records'] if r['id'] == 'trefoil')
    source, packet = macro_of(trefoil['arms']['u1']['result'])
    assert verify_normal_pachner_descent(source, packet)
    def field_zero(packet, field, value):
        packet['certificate']['moves'][0]['transport'][field][0][0] = value
    def outer_label(packet):
        packet['successor'] = deepcopy(packet['successor'])
        face = next(face for tet in packet['successor']['tetrahedra'] for face in tet if face is not None)
        face['tetrahedron'] = float(face['tetrahedron'])
    macro_mutations = [
        ('macro missing field', lambda p: p.pop('successor')),
        ('macro unknown field', lambda p: p.update(extra=0)),
        ('macro wrong source digest', lambda p: p.update(source_sha256='0'*64)),
        ('macro bool upward allowance', lambda p: p['certificate'].update(max_upward=True)),
        ('macro larger upward allowance', lambda p: p['certificate'].update(max_upward=2)),
        ('macro bool intermediate height', lambda p: field_zero(p,'heights',False)),
        ('macro float intermediate coordinate', lambda p: field_zero(p,'coordinates',0.0)),
        ('macro nonzero intermediate height', lambda p: field_zero(p,'heights',1)),
        ('macro bool formal height', lambda p: p['certificate']['moves'][0]['transport']['bipyramid_heights'].__setitem__(0,False)),
        ('macro nonzero Euler jump', lambda p: p['certificate']['moves'][0]['transport'].update(euler_jump=1)),
        ('macro disc payload', lambda p: p['certificate'].update(disc_certificate={})),
        ('macro deleted expansion', lambda p: p['certificate']['moves'].pop(0)),
        ('macro float outer successor label', outer_label),
    ]
    for name, mutate in macro_mutations:
        changed = deepcopy(packet)
        mutate(changed)
        reject(name, lambda changed=changed: verify_normal_pachner_descent(source, changed))

    # These early rejection controls do not rerun all archived native proofs.
    audit_mutations = [
        ('audit false completion', lambda x: x.update(passed=False)),
        ('audit wrong current pins', lambda x: x['source_sha256'].pop(next(iter(x['source_sha256'])))),
        ('audit missing case', lambda x: x['records'].pop()),
        ('audit duplicate case', lambda x: x['records'].__setitem__(1,deepcopy(x['records'][0]))),
        ('audit reordered cases', lambda x: x['records'].__setitem__(slice(0,2),list(reversed(x['records'][:2])))),
        ('audit unreturned call', lambda x: x['unreturned_calls'].append({'id':'T27'})),
        ('audit active call', lambda x: x.update(active_call={'id':'W34'})),
        ('audit recorded failure', lambda x: x['failures'].append({'id':'TT'})),
    ]
    for name, mutate in audit_mutations:
        changed = deepcopy(audit)
        mutate(changed)
        reject(name, lambda changed=changed: check_audit(changed))
    changed = deepcopy(audit)
    changed['coverage']['ordinary_calls_completed'] = 13
    reject('endpoint binding incomplete coverage', lambda: check_endpoint_bindings(changed))
    changed = deepcopy(audit)
    changed['coverage']['ordinary_calls_completed'] = True
    reject('endpoint binding bool coverage', lambda: check_endpoint_bindings(changed))

    # A legitimate same-diagram negative proof on the baseline source remains
    # native-valid in a v4 chain; it is deliberately the wrong experimental endpoint.
    alternate = deepcopy(trefoil['arms']['baseline']['result'])
    alternate['certificate']['chain']['schema'] = 'diagram-crushing-v4'
    for key in ('calls','nodes','work','macros','upward_moves','downward_moves'):
        alternate['stats']['pachner_descent_'+key] = 0
    knot = Diagram.from_pd(trefoil['input_pd'])
    assert verify_crushing_recognition(knot, alternate['certificate'])
    alternate_replay = replay_result(knot, 'u1', alternate, configs('u1'))
    changed = deepcopy(audit)
    target = next(r for r in changed['records'] if r['id'] == 'trefoil')
    target['arms']['u1'] = dict(result=alternate, replay=alternate_replay)
    reject('native-valid alternate endpoint', lambda: check_endpoint_bindings(changed))
    assert len({r['name'] for r in records}) == len(records)
    assert source_hashes() == pins
    output = dict(passed=True, valid_control=True, rejected_mutations=len(records),
        native_valid_alternate_endpoint=True, endpoint_bindings=12,
        scope='Genuine saved circle/macro controls, audit coverage and native-valid alternate-source binding challenge; no discovery or timing.',
        source_sha256=pins, fixture_sha256=sha256(raw).hexdigest(), audit_sha256=sha256(audit_bytes).hexdigest(),
        endpoint_helper_sha256=sha256((DATA/'pachner_descent_endpoint_binding.py').read_bytes()).hexdigest(),
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), records=records)
    args.output.write_text(json.dumps(output, sort_keys=True, indent=2)+'\n')
    print(json.dumps(dict(passed=True, valid_control=True, rejected_mutations=len(records),
                         native_valid_alternate_endpoint=True),sort_keys=True))


if __name__ == '__main__':
    main()
