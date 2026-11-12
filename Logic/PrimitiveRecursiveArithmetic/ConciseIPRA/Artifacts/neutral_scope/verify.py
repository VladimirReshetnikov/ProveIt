"""Offline verification of shipped programs and actual public CLI verdicts."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import tempfile
import measure

ROOT = Path(__file__).resolve().parent


def accepts(program, packet, optimized=False, raw=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(program)]
    result = subprocess.run(command, input=packet if raw else json.dumps(packet),
                            text=True, capture_output=True, timeout=15)
    return result.returncode == 0 and result.stdout == 'ACCEPT\n'


def verify(write=False):
    manifest = ROOT / 'MANIFEST.json'
    if manifest.exists():
        for item in json.loads(manifest.read_text())['files']:
            data = (ROOT / item['path']).read_bytes()
            if hashlib.sha256(data).hexdigest() != item['sha256']:
                raise ValueError('Manifest mismatch: ' + item['path'])
    metrics = measure.main(False)
    if metrics['corpus_metric_mismatches']:
        raise ValueError('Corpus measurements differ on this runtime; run measure.py.')
    cases = json.loads((ROOT / 'tests/cases.json').read_text())
    rows = []
    for name in ['checker.py', 'checker_explicit.py', 'checker_ast.py', 'readable_checker.py']:
        program = ROOT / 'code' / name
        generic = name == 'checker_ast.py'
        for case in cases:
            for optimized in (False, True):
                actual = accepts(program, case['packet'], optimized)
                rows.append({'program': name, 'case': case['name'],
                             'optimized': optimized, 'expected': case['accept'],
                             'actual': actual, 'ok': actual == case['accept']})
        roots = [('', 'empty_input', False), ('{}', 'object_input', False),
                 ('null', 'null_input', False), ('true', 'boolean_input', False),
                 ('42', 'number_input', False), ('"x"', 'string_input', False),
                 ('["x"]', 'nonempty_string_goal', False),
                 ('[[]]', 'empty_array_truth', True), ('[0]', 'scalar_fake_truth', False),
                 ('[[0,[0]]]', 'false_equation', False),
                 ('[[[-0.5],0]]', 'free_fractional_parameter', False),
                 ('[[true,0,0,0],[0,[0]]]', 'malformed_packet', False),
                 ('[""]', 'empty_string_alias', generic),
                 ('[{}]', 'empty_object_alias', generic)]
        for packet, label, expected in roots:
            for optimized in (False, True):
                actual = accepts(program, packet, optimized, True)
                rows.append({'program': name, 'case': label, 'optimized': optimized,
                             'expected': expected, 'actual': actual, 'ok': actual == expected})
        attack = json.loads((ROOT / 'tests/scalar_context_attack.json').read_text())
        for optimized in (False, True):
            actual = accepts(program, attack, optimized)
            rows.append({'program': name, 'case': 'scalar_context_attack',
                         'optimized': optimized, 'expected': False,
                         'actual': actual, 'ok': not actual})

    mutations = []
    with tempfile.TemporaryDirectory() as tmp:
        source = (ROOT / 'code/checker.py').read_text()
        assert 'g=[[]]' in source
        mutant = Path(tmp) / 'unsound_scalar_context.py'
        mutant.write_text(source.replace('g=[[]]', 'g=[0]'))
        for optimized in (False, True):
            mutations.append({'control': 'scalar_context', 'optimized': optimized,
                              'mutant_accepts_false': accepts(mutant, attack, optimized)})
        source = (ROOT / 'code/checker_ast.py').read_text()
        assert 'g=([],)' in source
        mutant = Path(tmp) / 'unsound_mutable_context.py'
        mutant.write_text(source.replace('g=([],)', 'g=[[]]'))
        leak = json.loads((ROOT / 'tests/context_leak_attack.json').read_text())
        for optimized in (False, True):
            mutations.append({'control': 'mutable_context', 'optimized': optimized,
                              'correct_rejects': not accepts(ROOT / 'code/checker_ast.py', leak, optimized),
                              'mutant_accepts_false': accepts(mutant, leak, optimized)})

    result = {'runs': len(rows), 'accepts': sum(r['actual'] for r in rows),
              'rejects': sum(not r['actual'] for r in rows),
              'mismatches': [r for r in rows if not r['ok']],
              'mutations': mutations, 'rows': rows,
              'frozen_sources_remeasured': metrics['frozen_sources']}
    if write:
        (ROOT / 'evidence/validation.json').write_text(json.dumps(result, indent=2) + '\n')
    if result['mismatches'] or any(not r['mutant_accepts_false'] or
                                  not r.get('correct_rejects', True) for r in mutations):
        raise ValueError(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    result = verify('--write' in sys.argv)
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}, indent=2))
