#!/usr/bin/env python3
"""Record the 14-variable comparator subprocess result and immutable inputs."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

D = Path(__file__).resolve().parent
assert len(sys.argv) in (5, 6), 'usage: run.py PLAN AUTHOR PEER PARENT_COMPARATOR_RECEIPT [EXPECTED_RECEIPT]'
plan, author, peer, parent_receipt = (Path(x).absolute() for x in sys.argv[1:5])
expected = Path(sys.argv[5]).absolute() if len(sys.argv) == 6 else None
assert author.resolve() != peer.resolve() and not os.path.samefile(author / 'state.json', peer / 'state.json'), \
       'author and peer must be independent runs'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = [Path(__file__).resolve(), D / 'compare.py', plan / 'manifest.json', plan / 'replay.py',
          author / 'state.json', peer / 'state.json', parent_receipt]
if expected is not None:
    inputs.append(expected)
before = {str(p.resolve()): H(p) for p in inputs}
log, terminal, receipt = D / 'run.log', D / 'terminal.json', D / 'receipt.json'
assert not any(os.path.lexists(p) for p in (log, terminal, receipt)), 'refusing to overwrite evidence'
result = {'status': 'FAIL', 'comparator_exit_code': None, 'before': before}
try:
    with log.open('x') as out:
        proc = subprocess.run([sys.executable, str(D / 'compare.py'), str(plan), str(author),
                               str(peer), str(parent_receipt)], stdout=out, stderr=subprocess.STDOUT)
    result['comparator_exit_code'] = proc.returncode
    after = {str(p.resolve()): H(p) for p in inputs}
    result.update(after=after, log_sha256=H(log))
    if receipt.is_file():
        receipt_hash = H(receipt)
        result['receipt_sha256'] = receipt_hash
        data = json.loads(receipt.read_text())
        pm = json.loads((plan / 'manifest.json').read_text())
        expected_log = (f"MATCHED_PASS 11 rows {data['guarded_file_count']} files "
                        f"workspace_matches {data['workspace_matches_snapshot_through_observations']}\n")
        ok = (proc.returncode == 0 and before == after and data.get('status') == 'MATCHED_PASS'
              and data.get('rows') == 11 and data.get('compare_sha256') == H(D / 'compare.py')
              and data.get('manifest_sha256') == H(plan / 'manifest.json')
              and data.get('driver_sha256') == H(plan / 'replay.py')
              and data.get('parent_comparator_sha256') == H(parent_receipt)
              and data.get('parent_comparator_receipt') == str(parent_receipt)
              and pm['parent_comparison_receipt_sha256'] == H(parent_receipt)
              and pm['parent_comparison_receipt_path'] == str(parent_receipt)
              and data.get('author_state_sha256') == H(author / 'state.json')
              and data.get('peer_state_sha256') == H(peer / 'state.json')
              and log.read_text() == expected_log and H(receipt) == receipt_hash)
        if expected is not None:
            result['expected_receipt_sha256'] = H(expected)
            ok = ok and receipt_hash == H(expected)
        ok = ok and before == {str(p.resolve()): H(p) for p in inputs}
        if ok:
            result['status'] = 'PASS_COMPARATOR_EXIT_0'
except BaseException as exc:
    result['exception'] = repr(exc)
with terminal.open('x') as out:
    json.dump(result, out, sort_keys=True, indent=2)
    out.write('\n')
print(result['status'], flush=True)
if result['status'] != 'PASS_COMPARATOR_EXIT_0':
    raise SystemExit(1)
