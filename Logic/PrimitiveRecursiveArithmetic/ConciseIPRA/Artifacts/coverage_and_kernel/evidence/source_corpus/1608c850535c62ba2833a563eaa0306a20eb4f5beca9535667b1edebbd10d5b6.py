"""Reproduce complete-program comparison; never imports a proof checker."""
from pathlib import Path
import hashlib
import json
import platform
import runpy

ROOT = Path(__file__).resolve().parent
metrics = runpy.run_path(str(ROOT / 'reference/source_measure.py'))['metrics']
saved = json.loads((ROOT / 'evidence/metrics.json').read_text())
keys = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')
for group in ('baseline', 'candidates', 'successor_candidates'):
    for row in saved[group]:
        actual = metrics(ROOT / row['local_file'])
        for field in (*keys, 'sha256'):
            if actual[field] != row[field]:
                raise SystemExit('Measurement mismatch: ' + row['local_file'] + '/' + field)
corpus = json.loads((ROOT / 'evidence/all_python_sources.json').read_text())
checked = set()
for entry in corpus['occurrences']:
    if entry['sha256'] in checked:
        continue
    path = ROOT / entry['local_file']
    if hashlib.sha256(path.read_bytes()).hexdigest() != entry['sha256']:
        raise SystemExit('Corpus source changed: ' + entry['source_file'])
    old = corpus['measurements'][entry['sha256']]
    if 'parse_error' not in old:
        actual = metrics(path)
        if any(actual[k] != old[k] for k in keys):
            raise SystemExit('Corpus metric changed: ' + entry['source_file'])
    checked.add(entry['sha256'])
result = {'status': 'PASS', 'python': platform.python_version(),
          'comparators': len(saved['baseline']), 'candidates': len(saved['candidates']) + len(saved['successor_candidates']),
          'distinct_corpus_sources': len(checked),
          'old_envelope': saved['old_envelope'], 'new_envelope': saved['new_envelope'], 'combined_envelope': saved['combined_envelope'],
          'single_program_dominates_old_envelope': saved['one_program_dominates']}
(ROOT / 'evidence/measurement_replay.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
