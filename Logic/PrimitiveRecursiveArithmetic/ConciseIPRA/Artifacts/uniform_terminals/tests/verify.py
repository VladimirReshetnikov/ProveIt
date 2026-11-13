"""Reproduce metrics, proof-trace translations, and isolated checker outcomes.

Only Python's standard library is needed. No network or repository checkout
is used. The measured acceptance modules import none of these utilities.
"""
import ast
import concurrent.futures
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
from translate import array, jsonl, stream

ROOT = Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
        tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}
PROGRAMS = {
    'code/controls/checker_tokens243.py': (243, 271, 616),
    'code/controls/checker_ast264.py': (248, 264, 613),
    'code/controls/checker_bytes474.py': (270, 308, 474),
    'code/checker_tokens.py': (242, 268, 565),
    'code/checker_ast.py': (247, 263, 553),
    'code/checker_bytes.py': (272, 306, 469),
}


def measure(relative):
    raw = (ROOT / relative).read_bytes()
    tree = ast.parse(raw)
    normalized = ast.unparse(tree) + '\n'
    encoded = normalized.encode()
    return {'file': relative,
            'significant_tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_utf8_bytes': len(encoded),
            'source_utf8_bytes': len(raw),
            'normalized_gzip9_mtime0_bytes': len(gzip.compress(encoded, compresslevel=9, mtime=0)),
            'source_gzip9_mtime0_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(encoded).hexdigest()}


def replay_translation(entry):
    source = (ROOT / entry['source']).read_bytes()
    if entry['mode'] == 'bytes':
        result, statistics = array(json.loads(source))
        result = (json.dumps(result, separators=(',', ':')) + '\n').encode()
    else:
        records = [json.loads(line) for line in source.splitlines() if line.strip()]
        result, statistics = stream(records, entry['mode'] == 'ast')
        result = jsonl(result)
    return {'source': entry['source'], 'target': entry['target'],
            'mode': entry['mode'], 'statistics': statistics,
            'exact_output_match': result == (ROOT / entry['target']).read_bytes(),
            'statistics_match': statistics == entry['statistics']}


def input_bytes(case):
    data = (ROOT / case['fixture']).read_bytes()
    if 'mutation' not in case:
        return data
    false_goal = [0, [0]] if case['mutation'] == 'false_zero_one' else [[[5, 0, 7], [5, 0, [11]]]]
    if case['framing'] == 'stream':
        rows = [json.loads(line) for line in data.splitlines() if line.strip()]
        rows[0] = false_goal
        return jsonl(rows)
    rows = json.loads(data)
    rows[-1] = [false_goal, 0]
    return (json.dumps(rows, separators=(',', ':')) + '\n').encode()


def execute(job):
    case, optimized = job
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / case['program']))
    data = input_bytes(case)
    timed_out = False
    try:
        result = subprocess.run(command, input=data, capture_output=True, timeout=20)
        accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    except subprocess.TimeoutExpired:
        accepted, timed_out = False, True
    return {'case': case['name'], 'program': case['program'], 'kind': case['kind'],
            'fixture': case['fixture'], 'optimized': optimized,
            'expected': case['expected'], 'accepted': accepted, 'timed_out': timed_out,
            'passed': accepted == case['expected'] and not timed_out,
            'input_sha256': hashlib.sha256(data).hexdigest()}


def main():
    modules = [measure(p) for p in PROGRAMS]
    measurements_pass = True
    if sys.version_info[:2] == (3, 12):
        for row in modules:
            actual = tuple(row[k] for k in ('significant_tokens', 'ast_nodes', 'normalized_utf8_bytes'))
            if actual != PROGRAMS[row['file']]:
                measurements_pass = False
    metrics = {'python': sys.version, 'reference_python': 'CPython 3.12.14',
               'normalization': "ast.unparse(ast.parse(source)) + '\\n'",
               'gzip': 'gzip.compress(normalized_utf8, compresslevel=9, mtime=0)',
               'modules': modules, 'old_coordinate_envelope': [243, 264, 474],
               'new_coordinate_envelope': [242, 263, 469],
               'one_program_attains_all_coordinate_minima': False,
               'reference_metrics_match': measurements_pass,
               'compact_contract': 'Canonical closed guarded Eq/D public goals and finite exact integer/list certificate data are promised. See paper for explicit differing stream/array framings.'}
    translations = [replay_translation(e) for e in json.loads((ROOT / 'tests/translations.json').read_text())]
    cases = json.loads((ROOT / 'tests/cases.json').read_text())
    jobs = [(case, optimized) for case in cases for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        outcomes = list(pool.map(execute, jobs))
    failures = [r for r in outcomes if not r['passed']]
    translation_failures = [r for r in translations if not r['exact_output_match'] or not r['statistics_match']]
    receipt = {'python': sys.version, 'case_count': len(cases), 'process_executions': len(outcomes),
               'translation_count': len(translations),
               'fixed_point_checks_in_replayed_translations': sum(r['statistics']['fixed_point_checks'] for r in translations),
               'failures': failures, 'translation_failures': translation_failures,
               'translations': translations, 'outcomes': outcomes,
               'proof_status': 'Finite implementation evidence; not a mechanized proof of the universal soundness/completeness or bi-interpretation results.'}
    (ROOT / 'evidence/metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    (ROOT / 'evidence/verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'reference_metrics_match': measurements_pass,
                      'new_coordinate_envelope': metrics['new_coordinate_envelope'],
                      'process_executions': len(outcomes), 'translations': len(translations),
                      'failed_process_expectations': len(failures),
                      'failed_translations': len(translation_failures)}, indent=2))
    if not measurements_pass or failures or translation_failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
