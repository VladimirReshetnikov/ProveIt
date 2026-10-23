#!/usr/bin/env python3
"""Integrity and receipt binding checks; does not run a proof assistant."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    observed={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
    if observed != set(manifest):raise SystemExit('Package membership mismatch')
    for name,record in manifest.items():
        p=ROOT/name
        if sha(p)!=record['sha256'] or p.stat().st_size!=record['bytes']:
            raise SystemExit('Package hash mismatch: '+name)
    record=json.loads((ROOT/'evidence/final/receipt.json').read_text())
    if record['status']!='PASS_COMPONENT' or len(record['checks'])!=11:
        raise SystemExit('Unexpected receipt scope/status')
    for item in record['inputs']:
        p=(ROOT/'deps'/item['build_path']) if 'repo_path' in item else (ROOT/item['local_path'])
        if sha(p)!=item['sha256']:raise SystemExit('Compiled input mismatch: '+str(p))
    for check in record['checks']:
        p=ROOT/'evidence/final'/check['log']
        if check['exit_code']!=0 or sha(p)!=check['log_sha256']:
            raise SystemExit('Failed or changed compiler receipt')
    audit=record['checks'][-1]['command']
    if audit[-1]!='Runtime215Locality' or any(x in audit for x in ['-admit','-norec']):
        raise SystemExit('Unexpected recursive audit target/options')
    reports=''.join((ROOT/'evidence/final/logs'/name).read_text() for name in ['FootprintReplay.v.log','Runtime215Locality.v.log'])
    if reports.count('Closed under the global context')!=5 or 'Axioms:' in reports:
        raise SystemExit('Unexpected new-theorem assumption reports')
    if list(ROOT.rglob('*.vo')):raise SystemExit('Compiled objects must not be shipped')
    print('PASS: package integrity, ten compiled-source bindings, eleven successful process receipts, five closed new-theorem reports')
    print('This is a saved-receipt check, not a fresh proof-assistant replay.')
if __name__=='__main__':main()
