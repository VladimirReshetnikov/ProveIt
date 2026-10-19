#!/usr/bin/env python3
"""Check pinned K230 bytes and the provenance of the supplied upstream CI receipt.

This is a local data audit, not a local invocation of the Rocq compiler.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
COMMIT = '3142e4dd980f0be12f4abb636c4ae2528afc17eb'
TABLE = 'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8'
SITES = '400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
MANIFEST = 'bbd4694416cef144c8cad8099148a08c5a81114a81e358ad3f0d2dd5cdea6119'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    upstream = ROOT / 'vendor/k230-rocq'
    ci = ROOT / 'evidence/upstream-ci'
    manifest_path = upstream / 'manifest.json'
    require(sha(manifest_path) == MANIFEST, 'Upstream manifest pin')
    manifest = json.loads(manifest_path.read_text())
    for path, expected in manifest['local_files'].items():
        require(sha(upstream/path) == expected, 'Upstream local file changed: '+path)
    require(sha(upstream/'machine/k230.tm') == TABLE, 'Table pin')
    require(sha(upstream/'machine/sites230.json') == SITES, 'Source pin')

    text_rows = {}
    for line in (upstream/'machine/k230.tm').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        key = int(q), int(b)
        require(key not in text_rows, 'Duplicate text transition')
        text_rows[key] = int(w), d, int(z)
    require(set(text_rows) == {(q,b) for q in range(230) for b in (0,1)},
            'K230 transition census')
    pattern = (r'\((true|false),\s*([LR]),\s*(\d+),\s*'
               r'(true|false),\s*([LR]),\s*(\d+)\)\s*;?\s*\(\*\s*(\d+)\s*\*\)')
    literal_rows = {}
    for a, d, z, b, e, t, q in re.findall(pattern, (upstream/'coq/tm/Table230.v').read_text()):
        q = int(q)
        require((q,0) not in literal_rows, 'Duplicate Rocq state')
        literal_rows[q,0] = int(a == 'true'), d, int(z)
        literal_rows[q,1] = int(b == 'true'), e, int(t)
    require(literal_rows == text_rows, 'Text/Rocq literal table mismatch')

    verification = json.loads((ci/'verification-result.json').read_text())
    kernel = json.loads((ci/'coqchk-result.json').read_text())
    require(verification['status'] == kernel['status'] == 'PASSED', 'CI result status')
    require(verification['manifest_sha256'] == MANIFEST and
            verification['machine_sha256'] == TABLE, 'CI byte pins')
    require(verification['reference_commit'] == manifest['reference']['commit'], 'CI dependency pin')
    require(verification['compiled'] == manifest['compile_order'], 'CI compile order')
    require(verification['closed_reports'] == 2, 'CI endpoint assumptions reports')
    require(kernel['exit_code'] == 0 and kernel['target'] == 'K230.Correct230', 'CI kernel endpoint')
    require(kernel['log_sha256'] == sha(ci/'coqchk.log'), 'CI kernel log hash')
    output = dict(status='PINNED_UPSTREAM_DATA_AUDIT_PASS',
                  commit=COMMIT, table_sha256=TABLE, sites_sha256=SITES,
                  manifest_sha256=MANIFEST, local_file_hashes_checked=len(manifest['local_files']),
                  literal_Rocq_transition_rows_checked=len(literal_rows),
                  external_CI_run=39258562285, external_CI_artifact=12192455062,
                  external_compiled_sources=len(verification['compiled']),
                  external_closed_endpoint_reports=2, external_coqchk_exit_code=0,
                  fresh_local_Rocq_build=False,
                  scope='Local byte and literal-table audit. The supplied compiler and kernel logs '
                        'are upstream GitHub Actions evidence at the pinned commit; this script '
                        'does not compile any Rocq source or independently recreate that CI run.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
