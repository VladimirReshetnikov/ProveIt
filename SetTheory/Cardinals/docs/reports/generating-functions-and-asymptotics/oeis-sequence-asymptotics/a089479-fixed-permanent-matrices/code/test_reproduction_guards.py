#!/usr/bin/env python3
"""Negative tests for exact effective-error, input tables, and provenance guards."""
from copy import deepcopy
import json
from pathlib import Path
import shutil
import sys
import tempfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from check_effective_error import generate as effective, interval
from decimal_diagnostics import evaluate
from check_precomputed_audits import generate as audits
import verify_frozen_sources


def run_tests():
    rejected = []
    def bad(label, operation):
        try:
            operation()
        except (ArithmeticError, ValueError, KeyError, OSError, TypeError):
            rejected.append(label)
        else:
            raise ArithmeticError('guard failed: '+label)
    certificate = json.loads((ROOT/'code/constant_certificate.json').read_text())
    exact = json.loads((ROOT/'certificates/exact_checks.json').read_text())
    if effective(certificate, exact)['status'] != 'PASS':
        raise ArithmeticError('valid effective check rejected')
    for key, val in [('rho', ['1.51', '1.52']), ('P2_binomial1', ['-50', '-49']),
                     ('P3_binomial2', ['0', '0.1']), ('P4_binomial3', ['1.2', '1.21'])]:
        changed = deepcopy(certificate)
        changed[key]['outward_decimal_25'] = val
        bad('changed certificate '+key, lambda changed=changed: effective(changed, exact))
    wrong = deepcopy(exact)
    wrong['counts']['2'][0] = 10**20
    bad('changed count', lambda: effective(certificate, wrong))
    for value in ([], ['2', '1'], ['one', 'two']):
        bad('invalid interval '+repr(value), lambda value=value: interval({'x': {'outward_decimal_25': value}}, 'x'))
    for derivative in (-1, 5, 1.5, '1'):
        bad('Decimal derivative '+repr(derivative), lambda derivative=derivative: evaluate([1], 1, derivative))
    with tempfile.TemporaryDirectory(prefix='fixed-permanent-guards-') as temporary:
        work = Path(temporary)
        optional = work/'optional'
        shutil.copytree(ROOT/'optional', optional)
        if audits(optional)['status'] != 'PASS':
            raise ArithmeticError('valid precomputed audit rejected')
        original = (optional/'audit_counts.tsv').read_text()
        for label, content in [('header', original.replace('mode\t', 'wrong\t', 1)),
                               ('duplicate row', original+original.splitlines()[1]+'\n'),
                               ('row count', original.replace('all_binary\t1\t0\t1', 'all_binary\t1\t0\t2'))]:
            (optional/'audit_counts.tsv').write_text(content)
            bad('audit '+label, lambda: audits(optional))
        (optional/'audit_counts.tsv').write_text(original)
        block = (optional/'audit_block_counts.tsv').read_text()
        (optional/'audit_block_counts.tsv').write_text(block+block.splitlines()[1]+'\n')
        bad('duplicate block row', lambda: audits(optional))
        fixture = work/'frozen'
        fixture.mkdir()
        for name in list(verify_frozen_sources.EXPECTED)+['data/FROZEN_SOURCE_HASHES.json']:
            destination = fixture/name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes((ROOT/name).read_bytes())
        if verify_frozen_sources.verify(fixture)['status'] != 'PASS':
            raise ArithmeticError('valid frozen provenance rejected')
        p = fixture/'code/check_fixed_permanent.py'
        p.write_bytes(p.read_bytes()+b'\n')
        bad('frozen altered source', lambda: verify_frozen_sources.verify(fixture))
        p.write_bytes((ROOT/'code/check_fixed_permanent.py').read_bytes())
        receipt = fixture/'data/FROZEN_SOURCE_HASHES.json'
        data = json.loads(receipt.read_text())
        data['files'].pop('optional/audit_counts.cpp')
        receipt.write_text(json.dumps(data))
        bad('frozen missing inventory', lambda: verify_frozen_sources.verify(fixture))
    return {'status': 'PASS', 'negative_tests': len(rejected), 'positive_tests': 3,
            'assertions_required': False}


if __name__ == '__main__':
    print(json.dumps(run_tests(), sort_keys=True))
