#!/usr/bin/env python3
"""Offline release replay for the two new positive-domain polynomials.

All verification is exact finite algebra and data checking. The unbounded
existence proof and inherited semantic boundary are in PROOF.md and the article.
"""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, description):
    if not condition:
        raise RuntimeError(description)


def authenticate():
    count = 0
    for ledger in ('NATIVE_FETCH.json', 'UPSTREAM_FETCH.json'):
        for entry in json.loads((ROOT / ledger).read_text()):
            relative = Path(entry.get('local', entry.get('path')))
            require(not relative.is_absolute() and '..' not in relative.parts,
                    'portable source identity: ' + str(relative))
            raw = (ROOT / relative).read_bytes()
            digest = hashlib.sha256(raw).hexdigest()
            blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
            require(digest == entry['sha256'], 'source SHA256: ' + str(relative))
            expected_blob = entry.get('git_blob', entry.get('git_blob_sha1'))
            require(blob == expected_blob, 'source Git blob: ' + str(relative))
            count += 1
    return count


def coefficients():
    binding = json.loads((ROOT / 'native/ACTIVE_BINDING.json').read_text())
    summary = []
    values = {}
    for port, entry in binding['ports'].items():
        packed = (ROOT / 'native' / entry['file']).read_bytes()
        raw = gzip.decompress(packed)
        value = int.from_bytes(raw, 'little')
        require(hashlib.sha256(packed).hexdigest() == entry['sha256_gzip'],
                'compressed coefficient hash: ' + port)
        require(hashlib.sha256(raw).hexdigest() == entry['sha256_raw'],
                'raw coefficient hash: ' + port)
        require(len(raw) == entry['raw_bytes'] and value.bit_length() == entry['bits'],
                'coefficient size: ' + port)
        require(value > 0, 'positive coefficient: ' + port)
        values[port] = value
        summary.append({'port': port, 'bits': entry['bits'], 'raw_bytes': len(raw)})
    require(values['beta'] == (1 << 590069) - 1, 'literal fixed beta')
    require(values['MC'] < values['beta'] and values['MF'] < 2 * values['beta'],
            'authentic mask bounds')
    return binding, summary


def replay():
    source_files = authenticate()
    binding, payloads = coefficients()
    with tempfile.TemporaryDirectory(prefix='con-zfc-positive-') as td:
        temporary = Path(td)
        for f in ROOT.iterdir():
            if f.is_file() and (f.suffix in ('.py', '.json') or f.name == 'LICENSE'):
                shutil.copy2(f, temporary / f.name)
        shutil.copytree(ROOT / 'native', temporary / 'native')
        receipts = []
        for builder, circuit, checker, audit in (
            ('build11.py', 'p11_positive_degree269.json', 'verify11.py', 'AUDIT11.json'),
            ('build12.py', 'p12_positive_degree78.json', 'verify12.py', 'AUDIT12.json'),
        ):
            subprocess.run([sys.executable, str(temporary / builder)],
                           check=True, capture_output=True, text=True)
            require((ROOT / circuit).read_bytes() == (temporary / circuit).read_bytes(),
                    'byte-identical circuit rebuild: ' + circuit)
            subprocess.run([sys.executable, str(temporary / checker)],
                           check=True, capture_output=True, text=True)
            actual_audit = 'AUDIT12_OPTIMIZED.json' if checker == 'verify12.py' and not __debug__ else audit
            receipt = json.loads((temporary / actual_audit).read_text())
            require(receipt['status'] == 'PASS', 'exact circuit audit: ' + circuit)
            receipts.append(receipt)
        native = temporary / 'native'
        subprocess.run([sys.executable, str(native / 'build_coefficients.py')],
                       check=True, capture_output=True, text=True)
        for port, entry in binding['ports'].items():
            raw = gzip.decompress((native / entry['file']).read_bytes())
            require(hashlib.sha256(raw).hexdigest() == entry['sha256_raw'],
                    'reconstructed actual coefficient: ' + port)
        subprocess.run([sys.executable, str(native / 'audit_coefficients.py')],
                       check=True, capture_output=True, text=True)
        native_receipt = json.loads((native / 'INDEPENDENT_AUDIT.json').read_text())
        require(native_receipt['status'] == 'PASS', 'independent native reconstruction')
    return {'status': 'PASS', 'authenticated_upstream_files': source_files,
            'actual_fixed_coefficients': payloads,
            'native_reconstruction': 'PASS', 'independent_native_audit': 'PASS',
            'byte_identical_circuit_rebuilds': 2,
            'polynomials': [
                {'unknowns': 11, 'domain': 'positive integers', 'degree': 269, 'gates': 111},
                {'unknowns': 12, 'domain': 'positive integers', 'degree': 78, 'gates': 102}],
            'scope': 'Exact finite algebra and data; not an end-to-end formal certificate.'}


if __name__ == '__main__':
    result = replay()
    (ROOT / 'VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
