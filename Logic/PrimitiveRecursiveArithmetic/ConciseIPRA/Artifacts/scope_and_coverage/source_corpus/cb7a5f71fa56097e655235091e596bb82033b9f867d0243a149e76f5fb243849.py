"""Reproduce whole-program metrics, matched controls and frozen source census.

No historical checker is executed. Gzip is an informational metric.
Run with --write to refresh this package's comparison tables intentionally.
"""
import argparse
import gzip
import importlib.util
import json
import platform
import sys
import zlib
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


audit = load_module('source_audit', ROOT / 'evidence/audit_corpus.py')


def collect(verify_corpus=True):
    candidate_names = ('checker.py', 'checker_bytes.py', 'checker_joint.py')
    candidates = [{'file': name, **audit.measure((ROOT / 'code' / name).read_bytes())}
                  for name in candidate_names]
    old = json.loads((ROOT / 'evidence/corpus_metrics.json').read_text())
    if verify_corpus:
        for row in old['sources']:
            raw = (ROOT / 'reference/corpus_sources' / (row['sha256'] + '.py')).read_bytes()
            actual = audit.measure(raw)
            expected = {key: row[key] for key in actual}
            if actual != expected:
                raise ValueError('Corpus metric mismatch: ' + row['sha256'])
    classification = json.loads((ROOT / 'evidence/boundary_classification.json').read_text())
    metric_keys = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')
    source_index = {row['sha256']: row for row in old['sources']}
    boundary_checkers = [source_index[row['sha256']] for row in classification['sources']
                         if row['classification'] == 'complete_checker']
    supplied_minima = {key: min(row[key] for row in boundary_checkers)
                       for key in metric_keys}
    expected_boundary = {row['sha256'] for row in old['sources']
                         if any(row[key] <= supplied_minima[key] for key in metric_keys)}
    if expected_boundary != {row['sha256'] for row in classification['sources']}:
        raise ValueError('Incomplete boundary classification')
    control_module = load_module('matched_controls', ROOT / 'reference/controls/make_controls.py')
    controls = json.loads((ROOT / 'reference/controls/metrics.json').read_text())
    for control in controls:
        original = (ROOT / 'reference/controls' / control['frozen_original']).read_bytes()
        transformed = control_module.remove_wrapper(original.decode())
        matched = ROOT / 'reference/controls' / control['matched_file']
        if matched.read_bytes() != transformed:
            raise ValueError('Changed driver-only control: ' + str(matched))
        actual = audit.measure(transformed)
        if actual != {key: control['new'][key] for key in actual}:
            raise ValueError('Control measurement mismatch: ' + str(matched))
    matched_minima = {key: min(supplied_minima[key],
                              *(row['new'][key] for row in controls))
                      for key in metric_keys}
    for candidate in candidates:
        path = ROOT / 'code' / candidate['file']
        expected_gzip = gzip.compress(path.read_bytes(), compresslevel=9, mtime=0)
        if path.with_suffix('.py.gz').read_bytes() != expected_gzip:
            raise ValueError('Gzip source mismatch: ' + candidate['file'])
    return {'commit': classification['commit'], 'python': platform.python_version(),
            'implementation': platform.python_implementation(),
            'zlib': zlib.ZLIB_RUNTIME_VERSION, 'gzip_level': 9, 'gzip_mtime': 0,
            'corpus_archives': old['archive_count'], 'corpus_sources': len(old['sources']),
            'corpus_occurrences': old['occurrences'],
            'supplied_minima': supplied_minima,
            'matched_minima': matched_minima,
            'matched_control_count': len(controls), 'programs': candidates}


def latex_table(result):
    lines = [r'\begin{center}', r'\small', r'\begin{tabular}{lrrrr}',
             r'\toprule', r'Complete implementation & Tokens & AST & Bytes & Gzip-9\\',
             r'\midrule', r'Supplied coordinate minima & 268 & 300 & 616 & ---\\',
             r'Matched coordinate minima & 264 & 300 & 601 & ---\\', r'\midrule']
    labels = {'checker.py': 'New explicit list test',
              'checker_bytes.py': 'New byte profile',
              'checker_joint.py': 'New joint profile (qualified)'}
    for row in result['programs']:
        lines.append(f"{labels[row['file']]} & {row['normalized_tokens']} & "
                     f"{row['ast_nodes']} & {row['normalized_bytes']} & {row['gzip9_raw']}" + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}',
              r'All new raw-source lengths equal their normalized lengths. ',
              r'The two envelope rows are coordinatewise minima from different files; ',
              r'each new implementation row is one complete file.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = collect()
    if args.write:
        (ROOT / 'evidence/comparison.json').write_text(json.dumps(result, indent=2) + '\n')
        (ROOT / 'evidence/metrics_table.tex').write_text(latex_table(result))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
