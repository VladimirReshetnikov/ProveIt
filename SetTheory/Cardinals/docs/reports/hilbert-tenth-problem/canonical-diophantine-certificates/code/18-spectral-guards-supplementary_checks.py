"""Small-domain and malformed-input checks, separate from the main test counts."""
from __future__ import annotations
import copy
import json
from pathlib import Path
from spectral_guards import Mode, Sequence, build_certificate, verify_certificate
from quartic_compiler import compile_certificate, verify_export

ROOT = Path(__file__).resolve().parents[1]

def run() -> dict:
    assignments = 0
    for coefficient in (-2, 0, 3):
        for base in (1, 2, 5):
            for horizon in (0, 1, 3):
                sequence = Sequence((Mode(base, (coefficient,)),))
                certificate = build_certificate(sequence, horizon)
                assert verify_certificate(certificate)
                for bits in (None, max(1, horizon.bit_length())):
                    system = compile_certificate(certificate, bits)
                    assert not system.failed_residuals()
                    assert all(system.values[y] == system.values[b] ** system.values[t]
                               for b, t, y in system.power_atoms)
                    assignments += 1
    sequence = Sequence((Mode(1, (16,)), Mode(2, (-10,)), Mode(4, (1,))))
    certificate = build_certificate(sequence, 4)
    for change in ('horizon', 'base', 'coefficient', 'endpoint'):
        bad = copy.deepcopy(certificate)
        if change == 'horizon':
            bad['horizon'] = 4.1
        elif change == 'base':
            bad['modes'][0]['base'] = 1.1
        elif change == 'coefficient':
            bad['modes'][0]['coefficients'][0] = 16.1
        else:
            bad['charts'][0][0][0] = 0.1
        assert not verify_certificate(bad)
    for mode in ('quartic', 'quasi'):
        assert verify_export(ROOT / 'examples' / f'hidden_negative_{mode}.json')
    report = {
        'supplementary_single_mode_assignments': assignments,
        'fractional_input_rejections': 4,
        'bundled_serialized_exports_rechecked': 2,
        'status': 'All supplementary checks passed.',
        'note': 'Separate from the main validation/results.json counts.',
    }
    (ROOT / 'validation' / 'supplementary_checks.json').write_text(
        json.dumps(report, indent=2) + '\n')
    return report

if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
