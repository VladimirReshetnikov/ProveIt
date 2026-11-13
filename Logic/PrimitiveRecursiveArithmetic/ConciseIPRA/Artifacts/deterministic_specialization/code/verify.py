"""Replay proof translations, independent controls, CLI, and complete metrics."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
from concurrent.futures import ThreadPoolExecutor

import checker
import translate

ROOT = Path(__file__).resolve().parents[1]


def measure(path):
    tree = ast.parse(path.read_text())
    if ast.get_docstring(tree) is not None:
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    count = sum(t.type not in ignored for t in
                tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    raw = path.read_bytes()
    destination = ROOT / 'code/normalized' / path.relative_to(ROOT)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(normalized)
    destination.with_suffix('.py.gz').write_bytes(gzip.compress(normalized, 9, mtime=0))
    return {'file': str(path.relative_to(ROOT)), 'normalized_bytes': len(normalized),
            'significant_tokens': count, 'ast_nodes': len(list(ast.walk(tree))),
            'gzip9_normalized_bytes': len(gzip.compress(normalized, 9, mtime=0)),
            'raw_bytes': len(raw), 'gzip9_raw_bytes': len(gzip.compress(raw, 9, mtime=0)),
            'source_sha256': hashlib.sha256(raw).hexdigest()}


def encoded(certificate):
    return json.dumps(certificate, separators=(',', ':')) + '\n'


def proof_nodes(proof):
    if proof[0] == 'r':
        return 1
    if proof[0] == 'x':
        return 1 + sum(proof_nodes(p) for p in proof[1:])
    if proof[0] == 'u':
        return 1 + proof_nodes(proof[-1])
    if proof[0] == 'e':
        return 1 + proof_nodes(proof[2]) + proof_nodes(proof[3])
    return 1 + proof_nodes(proof[3])


def invoke(job):
    name, program, raw, optimized = job
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / program)]
    result = subprocess.run(command, input=raw, text=True, capture_output=True, timeout=30)
    if result.returncode != 0 or result.stdout != 'ACCEPT\n':
        raise AssertionError((name, program, optimized, result.stderr))
    return {'case': name, 'program': program, 'optimized': optimized, 'accepted': True}


def main():
    target_dir = ROOT / 'code/translated_certificates'
    reverse_dir = ROOT / 'code/reverse_certificates'
    target_dir.mkdir(exist_ok=True)
    reverse_dir.mkdir(exist_ok=True)
    rows, jobs = [], []
    for path in sorted((ROOT / 'code/source_certificates').glob('*.json')):
        original = json.loads(path.read_text())
        translated = translate.translate(original)
        expanded = translate.expand(translated)
        if expanded['goal'] != original['goal']:
            raise AssertionError('Conclusion changed under the round trip')
        old_raw, new_raw, back_raw = map(encoded, (original, translated, expanded))
        (target_dir / path.name).write_text(new_raw)
        (reverse_dir / path.name).write_text(back_raw)
        rows.append({'case': path.stem,
                     'source_json_bytes': len(old_raw.encode()),
                     'target_json_bytes': len(new_raw.encode()),
                     'source_proof_nodes': proof_nodes(original['proof']),
                     'target_proof_nodes': proof_nodes(translated['proof'])})
        for optimized in (False, True):
            jobs.extend([(path.stem, 'reference/unrestricted.py', old_raw, optimized),
                         (path.stem, 'code/checker.py', new_raw, optimized),
                         (path.stem + ':reverse', 'reference/unrestricted.py', back_raw, optimized)])

    with ThreadPoolExecutor(max_workers=8) as pool:
        cli = list(pool.map(invoke, jobs))
    metrics = [measure(ROOT / path) for path in [
        'reference/unrestricted.py', 'reference/unrestricted_explicit.py',
        'reference/unrestricted_implicit.py', 'reference/deterministic_explicit.py',
        'code/checker.py', 'supplement/scope_fusion/control.py',
        'supplement/scope_fusion/checker.py']]
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    (evidence / 'metrics.json').write_text(json.dumps({'python': sys.version, 'programs': metrics}, indent=2) + '\n')
    result = {'status': 'passed', 'source_certificates': len(rows),
              'checked_forward_translations': len(rows), 'checked_reverse_expansions': len(rows),
              'cli_runs': len(cli), 'cases': rows, 'cli': cli}
    (evidence / 'translations.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ['status', 'source_certificates',
          'checked_forward_translations', 'checked_reverse_expansions', 'cli_runs']}))


if __name__ == '__main__':
    main()
