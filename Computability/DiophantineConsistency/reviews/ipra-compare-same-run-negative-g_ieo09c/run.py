#!/usr/bin/env python3
"""Run the comparison and retain its actual process exit and input hashes."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

D = Path(__file__).resolve().parent
assert len(sys.argv) in (4, 5), 'usage: run.py PLAN AUTHOR PEER [EXPECTED_RECEIPT]'
plan, author, peer = map(Path, sys.argv[1:4])
expected = Path(sys.argv[4]) if len(sys.argv) == 5 else None
assert author.resolve() != peer.resolve() and not os.path.samefile(
    author / 'state.json', peer / 'state.json'), 'author and peer must be independent runs'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = [Path(__file__).resolve(), D / 'compare.py', plan / 'manifest.json',
          plan / 'replay.py', author / 'state.json', peer / 'state.json']
if expected is not None:
    inputs.append(expected)
before = {str(p.resolve()): H(p) for p in inputs}
log, terminal, receipt = D / 'run.log', D / 'terminal.json', D / 'receipt.json'
assert not any(os.path.lexists(p) for p in (log, terminal, receipt)), 'refusing to overwrite evidence'
result = {'status': 'FAIL', 'comparator_exit_code': None, 'before': before}
try:
    with log.open('x') as out:
        proc = subprocess.run([sys.executable, str(D / 'compare.py'), str(plan),
                               str(author), str(peer)], stdout=out, stderr=subprocess.STDOUT)
    result['comparator_exit_code'] = proc.returncode
    after = {str(p.resolve()): H(p) for p in inputs}
    result.update(after=after, log_sha256=H(log))
    if receipt.is_file():
        receipt_hash = H(receipt)
        result['receipt_sha256'] = receipt_hash
        data = json.loads(receipt.read_text())
        pm = json.loads((plan / 'manifest.json').read_text())
        expected_log = (f"MATCHED_PASS 258 rows {data['guarded_file_count']} files "
                        f"workspace_matches {data['workspace_matches_snapshot_through_observations']}\n")
        ok = (proc.returncode == 0 and before == after and data.get('status') == 'MATCHED_PASS'
              and data.get('rows') == 258 and data.get('compare_sha256') == H(D / 'compare.py')
              and data.get('manifest_sha256') == H(plan / 'manifest.json')
              and data.get('driver_sha256') == H(plan / 'replay.py')
              and data.get('survey_manifest_sha256') == pm['survey_manifest_sha256']
              and data.get('author_state_sha256') == H(author / 'state.json')
              and data.get('peer_state_sha256') == H(peer / 'state.json')
              and log.read_text() == expected_log and H(receipt) == receipt_hash)
        if expected is not None:
            result['expected_receipt_sha256'] = H(expected)
            ok = ok and receipt_hash == H(expected)
        if ok:
            result['status'] = 'PASS_COMPARATOR_EXIT_0'
except BaseException as exc:
    result['exception'] = repr(exc)
with terminal.open('x') as out:
    json.dump(result, out, indent=2, sort_keys=True)
    out.write('\n')
print(result['status'], flush=True)
if result['status'] != 'PASS_COMPARATOR_EXIT_0':
    raise SystemExit(1)
