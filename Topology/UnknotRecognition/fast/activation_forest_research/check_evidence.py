"""Bind review outputs to source files and replay saved local/native packets."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
from unittest.mock import patch
from native_probe import (ROOT, cases, instance, reduce_core_three_handles,
                         replay_core_three_handles, verify_core_handlebody_certificate)
from activation_forest import verify_positive, verify_obstruction
from integration.parity_audit import exact_parity_defects
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.core_handlebody import select_core_forest


def main():
    data = ROOT/'synthesis/data'
    native = json.loads((data/'activation-forest-native-probe.json').read_text())
    relabel = json.loads((data/'activation-forest-relabel-probe.json').read_text())
    assert native['passed'] and relabel['passed']
    for name, digest in native['source_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    assert relabel['source_sha256'] == hashlib.sha256((Path(__file__).parent/'relabel_probe.py').read_bytes()).hexdigest()
    source_cases = cases()
    assert [c['id'] for c in source_cases] == [c['id'] for c in native['records']]
    positive = negative = parity = 0
    for case, row in zip(source_cases, native['records']):
        source = _prepare(case['triangulation'], lambda: None)
        geometry = _parallelity_geometry(source, _coordinates(source, case['coordinates'], lambda: None), lambda: None)
        _, old = reduce_core_three_handles(geometry)
        for trial in row['modes']:
            forest = [] if trial['mode'] == 'deferred' else select_core_forest(geometry['core'], strategy=trial['mode'])
            inst = instance(geometry, forest, old['dual_endpoints'])
            assert inst.digest() == trial['input_sha256']
            assert not exact_parity_defects(inst), (row['id'], trial['mode'])
            parity += 1
            if trial['status'] == 'SUCCESS':
                assert verify_positive(inst, trial['local_certificate'])
                with patch('fastunknot.core_three_handle_reduction.reduce_core_three_handles', side_effect=AssertionError('producer')):
                    reduced = replay_core_three_handles(geometry, trial['reduction'])
                    assert reduced is not None
                    assert verify_core_handlebody_certificate(reduced['core'], trial['core'])
                positive += 1
            else:
                assert trial['status'] == 'BLOCKED_EXACT'
                assert verify_obstruction(inst, trial['obstruction'])
                negative += 1
    assert (len(native['records']), positive, negative, parity) == (126, 366, 12, 378)
    assert len(relabel['records']) == 540 and relabel['hits'] == []
    assert Counter((x['mode'], x['before'], x.get('after')) for x in relabel['records']) == {
        ('source', 'COMPLETE', None): 178,
        ('source', 'INCONCLUSIVE', 'BLOCKED_EXACT'): 2,
        ('max_passages', 'COMPLETE', None): 180,
        ('deferred', 'COMPLETE', None): 180}
    algebra = json.loads((data/'activation-forest-delivered-audit.json').read_text())
    assert sum(algebra[k]['cases'] for k in ('exhaustive_4_by_2', 'random_matrix_graph')) == 8061
    assert sum(algebra[k]['SUCCESS'] for k in ('exhaustive_4_by_2', 'random_matrix_graph')) == 3117
    assert 'Ran 71 tests' in (data/'activation-forest-delivered-tests.txt').read_text()
    assert (data/'activation-forest-delivered-tests.txt').read_text().endswith('OK\n')
    files = [p for p in data.glob('activation-forest-*') if p.suffix in ('.json', '.txt') and p.name != 'activation-forest-evidence.json']
    files += list(Path(__file__).parent.glob('*.py'))
    files += [ROOT/'synthesis/representative_activation.tex', ROOT/'synthesis/report.pdf']
    result = dict(passed=True, authenticated_native_sources=126, positive_packets=positive,
                  exact_local_obstructions=negative, exact_parity_checks=parity,
                  relabelled_sources=180, relabelled_trials=540,
                  source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    (data/'activation-forest-evidence.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS: 126 native sources, 366 positive replays, 12 local obstructions, 378 exact parity checks; 540 relabelled trials.')


if __name__ == '__main__':
    main()
