"""Rebuild certificates, measure complete programs, and verify recorded checks.

Requires Python 3.12 for matching the pinned normalization measurements.
Run from any working directory: python3 /path/to/reproduce.py
No third-party Python packages, internet access, or external proof database.
"""
import ast
import csv
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence'
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def metric(path):
    tree = ast.parse(path.read_text())
    source = ast.unparse(tree) + '\n'
    data = source.encode()
    return dict(file=str(path.relative_to(ROOT)),
                significant_tokens=sum(t.type not in IGNORED for t in
                                       tokenize.generate_tokens(io.StringIO(source).readline)),
                ast_nodes=sum(1 for _ in ast.walk(ast.parse(source))),
                normalized_bytes=len(data),
                gzip9_bytes=len(gzip.compress(data, compresslevel=9, mtime=0)),
                normalized_sha256=hashlib.sha256(data).hexdigest())


def run(checker, data, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(checker)]
    try:
        result = subprocess.run(command, input=data, text=True,
                                capture_output=True, timeout=30)
        return result.returncode == 0 and result.stdout == 'ACCEPT\n'
    except subprocess.TimeoutExpired:
        return False


def verify_references():
    provenance = json.loads((ROOT / 'reference' / 'PROVENANCE.json').read_text())
    for row in provenance['files']:
        data = (ROOT / row['local']).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if actual != row['git_blob_sha']:
            raise ValueError('Pinned reference changed: ' + row['local'])
    return len(provenance['files'])


def main():
    reference_count = verify_references()
    subprocess.run([sys.executable, str(ROOT / 'tests' / 'generate.py')], check=True)
    paths = sorted((ROOT / 'code').glob('*.py')) + sorted((ROOT / 'reference').glob('*.py'))
    rows = [metric(path) for path in paths]
    metrics = dict(python=platform.python_version(), implementation=platform.python_implementation(),
                   zlib=zlib.ZLIB_RUNTIME_VERSION,
                   normalization='ast.unparse(ast.parse(source)) plus one LF; whole module',
                   gzip='compresslevel=9, mtime=0, wrapper included; informational only',
                   profiles=rows)
    (EVIDENCE / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    with (EVIDENCE / 'metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    latex = ['\\begin{tabular}{lrrrr}', '\\toprule',
             'Complete program & Tokens & AST nodes & Bytes & Gzip-9\\\\', '\\midrule']
    for row in rows:
        if row['file'].startswith('code/') and 'readable' not in row['file']:
            label = row['file'].split('/')[-1].replace('_', '\\_')
            latex.append('\\texttt{' + label + '} & ' + ' & '.join(str(row[k]) for k in
                         ['significant_tokens','ast_nodes','normalized_bytes','gzip9_bytes']) + '\\\\')
    latex += ['\\bottomrule', '\\end{tabular}']
    (EVIDENCE / 'metrics_table.tex').write_text('\n'.join(latex) + '\n')
    manifest = json.loads((EVIDENCE / 'certificate_manifest.json').read_text())
    checks = []
    profiles = [('checker.py','local'), ('checker_bytes.py','local'),
                ('checker_ast.py','local'), ('checker_tokens.py','global'),
                ('checker_strict.py','local'), ('readable_checker.py','local')]
    for checker, style in profiles:
        for optimized in [False, True]:
            for example in manifest:
                packet = ROOT / 'tests' / 'certificates' / example['packets'][style]['file']
                expected = example['canonical_goal'] or checker != 'checker_strict.py'
                accepted = run(ROOT / 'code' / checker, packet.read_text(), optimized)
                checks.append(dict(checker=checker, mode='-O' if optimized else 'normal',
                                   case=example['name'], expected=expected, accepted=accepted,
                                   passed=accepted == expected))
            for packet in sorted((ROOT / 'tests' / 'negative').glob('*.json')):
                if packet.name.startswith('old_atomic_case_') and not packet.name.endswith(style+'.json'):
                    continue
                accepted = run(ROOT / 'code' / checker, packet.read_text(), optimized)
                checks.append(dict(checker=checker, mode='-O' if optimized else 'normal',
                                   case=packet.stem, expected=False, accepted=accepted,
                                   passed=not accepted))
    # The old source-dispatch byte profile does accept this old atomic case.
    # This prevents a misleading claim that the two raw certificate languages
    # are identical: the equivalence theorem concerns PUBLIC consequences.
    control_data = (ROOT / 'tests' / 'negative' / 'old_atomic_case_local.json').read_text()
    for optimized in [False, True]:
        accepted = run(ROOT / 'reference' / 'source_checker.py', control_data, optimized)
        checks.append(dict(checker='reference/source_checker.py',
                           mode='-O' if optimized else 'normal', case='old_atomic_case_control',
                           expected=True, accepted=accepted, passed=accepted))
    report = dict(python=platform.python_version(), pinned_reference_files_verified=reference_count,
                  positive_examples=len(manifest), generated_certificates=2*len(manifest),
                  command_line_checks=len(checks), all_passed=all(c['passed'] for c in checks),
                  scope='Finite executable checks and source audits, not proof-assistant verification.',
                  checks=checks)
    (EVIDENCE / 'test_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key:value for key,value in report.items() if key!='checks'}, indent=2))
    failures = [c for c in checks if not c['passed']]
    if failures:
        print(json.dumps(failures, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
