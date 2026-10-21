"""Bind the independent portable comparison corpus to the primary artifacts."""
from pathlib import Path
import json
import subprocess
import sys


def run(root, work):
    corpus = root / 'research/comparison'
    assert (corpus / 'candidate.native.tm').read_bytes() == (root / 'machine/st215.native.tm').read_bytes()
    assert (corpus / 'source.sites.json').read_bytes() == (root / 'source/st215.sites.json').read_bytes()
    assert (corpus / 'runtime/runtime.json').read_bytes() == (root / 'evidence/runtime.json').read_bytes()
    out = work / 'independent-comparison'
    with (work / 'comparison.log').open('w') as log:
        subprocess.run([sys.executable, '-B', str(corpus / 'run_audits.py'),
                        '--out', str(out)], check=True, stdout=log, stderr=subprocess.STDOUT)
    checked = json.loads((out / 'audit.json').read_text())
    assert checked['status'] == 'FINITE_SOURCE_TABLE_PREFIX_GRAPH_AUDIT_PASS'
    assert checked['unique_215_table_bytes_compared'] == 78
    assert checked['named_215_tables_compared'] == 332
    assert checked['isomorphic_direct'] == checked['isomorphic_reflected'] == []
    control = checked['append_one_control']
    assert control['isomorphic_direct'] == control['isomorphic_reflected'] == []
    result = {'status': 'PASS', 'unique_comparison_files': 78,
              'named_215_tables_in_corpus': 332,
              'direct_or_reflected_matches': 0,
              'append_one_control_matches': 0,
              'scope': 'Rooted labelled transition graphs and finite metadata, not semantic inequivalence.'}
    (work / 'comparison.json').write_text(json.dumps(result, indent=2) + '\n')
    return result
