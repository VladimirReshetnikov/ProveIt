#!/usr/bin/env python3
"""Read-only audit of pinned v2 source hashes and retained non-Lean controls."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S without -O')
p=Path(__file__).resolve().parents[2]/'research/current14-printed-port-extension-driver-v2'
pins={'driver.py':'720a5a8ad2bb2cf05dafc5bd68afafbea9f452d343dbfb7e3b77628795492771','owned.py':'60859f538a7069d90f3f44871613fd2ef96c0ea738c9313cd1971d851b4b33ca','controls.py':'179b849afc41694da08a51d18401328294588a4541e8d7a08d7857e8d7762e18','guards.py':'e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3','controls-receipt.json':'6a1b2ae78c4fa4821135ad4ca39ec04a277ee2131cdcecc6cd3200dbabd71d27'}
for n,h in pins.items():
    if hashlib.sha256((p/n).read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch '+n)
r=json.loads((p/'controls-receipt.json').read_text())
if r['files_sha256']!={n:h for n,h in pins.items() if n!='controls-receipt.json'}:raise RuntimeError('receipt pin mismatch')
t=r['controls'];parsed=json.loads(t['stdout']);ref=r['running_base_refusal']
if t['exit']!=0 or t['stderr'] or parsed['status']!='PASS' or set(parsed['controls'])!={'monitor_failure_waits_for_group','threshold_owned_group_only','identity_mismatch_passively_waits','successful_owned_receipt'}:raise RuntimeError('control mismatch')
if ref['exit']==0 or 'base watchdog has not completed successfully' not in ref['stderr']:raise RuntimeError('base refusal mismatch')
print(json.dumps({'status':'PASS','pins':pins,'scope':'Read-only source-hash and retained-fixture receipt cross-check; no Lean or driver launch.'},sort_keys=True))
