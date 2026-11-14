#!/usr/bin/env python3
"""Replay finite preparation and pricing; check recorded search metadata."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
HERE = Path(__file__).resolve().parent

def verify():
    summary = json.loads((HERE / 'summary.json').read_text())
    for name, digest in summary['input_sha256'].items():
        assert hashlib.sha256((HERE / name).read_bytes()).hexdigest() == digest, name
    with tempfile.TemporaryDirectory(prefix='ax11g-grammar-check-') as d:
        output = Path(d)
        for script, directory in [('price_padding.py', 'padding'),
                                  ('price_safe_terminal.py', 'safe_terminal'),
                                  ('prepare.py', 'templates'),
                                  ('prepare_safe.py', 'templates')]:
            subprocess.run([sys.executable, '-B', str(HERE / script), '--output',
                            str(output / directory)], check=True,
                           stdout=subprocess.DEVNULL)
        pairs = [('padding/prices.json', 'recorded/padding/prices.json'),
                 ('padding/seeds.json', 'recorded/padding/seeds.json'),
                 ('safe_terminal/prices.json', 'recorded/safe_terminal/prices.json'),
                 ('templates/templates.txt', 'templates.txt'),
                 ('templates/safe_templates.txt', 'safe_templates.txt')]
        pairs += [('templates/' + n + '.tree.json', 'trees/' + n + '.tree.json')
                  for n in ['AX11G', 'node55', 'node58', 'node70']]
        for source, expected in pairs:
            assert (output / source).read_bytes() == (HERE / expected).read_bytes(), expected
            assert hashlib.sha256((HERE / expected).read_bytes()).hexdigest() == \
                summary['portable_preparation_and_pricing_replay']['checks'][expected]['sha256']
    for run in summary['runs']:
        log = (HERE / run['log']).read_text()
        assert f"INITIAL {run['initial_endings']} best 60 seed {run['seed']}" in log
        found = re.search(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([\d.]+)', log)
        assert found
        for key, value in zip(['iterations', 'accepted_mutations', 'hits', 'best_penalized_score'], found.group(1, 2, 3, 4)):
            assert run[key] == int(value), key
        assert run['recorded_seconds'] == float(found.group(5))
        assert len(list((HERE / 'recorded/final_seeds').glob(run['prefix'] + '.seed*.grammar.json'))) == 30
    return {'status': 'PASS', 'finite_outputs_reproduced_byte_for_byte': len(pairs),
            'input_hashes_checked': len(summary['input_sha256']),
            'recorded_runs_checked': len(summary['runs']),
            'stochastic_search_repeated': False,
            'scope': 'Portable finite preparation/pricing replay and recorded metadata; no global lower bound.'}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--receipt', type=Path)
    a = p.parse_args()
    result = verify()
    if a.receipt:
        a.receipt.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
