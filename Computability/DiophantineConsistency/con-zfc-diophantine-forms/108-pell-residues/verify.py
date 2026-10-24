#!/usr/bin/env python3
"""Independent release verification; delivered equation files are read-only.

Unbounded mathematics is proved in report.pdf and the proof notes. This script
checks the finite source binding, domain certificates, literal coefficients,
projections, secondary circuit identities, and arithmetic regression controls.
"""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'code'))
from release_support import command, parent_workspace, read, require, manifest_check


def verify():
    result = {'status':'pass', 'optimized_python':not __debug__,
              'scope':'Finite algebra and exact artifact binding; not a consistency proof by computation.'}
    result['manifest'] = manifest_check()
    source = ROOT/'equations/source655/equation.json'
    with parent_workspace() as parent:
        result['modular_structure'] = command(parent/'code/check_modular_structure.py',
            ROOT/'equations/source655/raw_audit_input.json', source)
        for name in ('natural395', 'natural394'):
            result[name] = command(ROOT/'code/check_natural.py',
                parent/'code/psd_contract/check.py', source, ROOT/'equations'/name)
    for name in ('integer663', 'integer687'):
        require(read(ROOT/'equations'/name/'source.json') == read(source),
                'Integer endpoint uses a different source')
        result[name] = command(ROOT/'code/integer_domain/check_mixed.py', ROOT/'equations'/name)
    result['modular_lemma_fixtures'] = command(ROOT/'code/verify_modular_lemmas.py')
    result['signed_pell_fixtures'] = command(ROOT/'code/check_signed_pell.py')
    result['twelve_integer'] = command(ROOT/'supplemental/integer12/check_centered12.py')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    result = verify()
    text = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text)
    print(text, end='')
