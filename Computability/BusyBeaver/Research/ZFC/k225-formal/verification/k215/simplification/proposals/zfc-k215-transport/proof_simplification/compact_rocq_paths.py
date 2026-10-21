#!/usr/bin/env python3
"""Render the unchanged 2240-entry Rocq certificate with binary path literals.

The input contains the exact pinned certificate in a lossless representation.
The emitted audit compares the entire compact certificate with the original
literal list by reflexivity. Neither the certificate checker nor its semantics
changes. Running this audit is not a replay of the full K215 endpoint.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

HELPER = '''(** Positive binary paths, with a high sentinel bit. Least-significant bit first. *)
Fixpoint certPath (p : positive) : list bool :=
  match p with
  | xH => []
  | xO q => false :: certPath q
  | xI q => true :: certPath q
  end.

'''


def bits(n):
    n = int(n)
    assert n >= 1
    out = []
    while n > 1:
        out.append('true' if n & 1 else 'false')
        n >>= 1
    return ';'.join(out)


def encode(bits_text):
    data = bits_text.split(';') if bits_text else []
    return str((1 << len(data)) + sum((1 << i) for i, b in enumerate(data) if b == 'true'))


def main():
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', type=Path, default=here / 'reference/cert215_encoded.json')
    ap.add_argument('--out', type=Path, default=here / 'rocq_pilot')
    ap.add_argument('--coqc', type=Path)
    ap.add_argument('--coqchk', type=Path)
    args = ap.parse_args()
    data = json.loads(args.input.read_text())
    entries, header, footer = data['entries'], data['header'], data['footer']
    assert len(entries) == 2240
    literal_rows = []
    compact_rows = []
    for i, (a, b, z, left, right) in enumerate(entries):
        pa, pb = bits(a), bits(b)
        assert encode(pa) == a and encode(pb) == b
        suffix = ';' if i + 1 < len(entries) else ''
        literal_rows.append(f'  ([{pa}], [{pb}], {z}%Z, {left}%N, {right}%N){suffix}')
        compact_rows.append(f'  (certPath {a}%positive, certPath {b}%positive, {z}%Z, {left}%N, {right}%N){suffix}')
    literal = header + '\n'.join(literal_rows) + footer
    compact = header.replace('Definition Cert215', HELPER + 'Definition Cert215') + '\n'.join(compact_rows) + footer
    assert len(literal.encode()) == 1499170
    assert len(compact.encode()) == 229933
    args.out.mkdir(parents=True, exist_ok=True)
    output = args.out / 'Cert215Offsets.v'
    output.write_text(compact)
    literal_decl = literal[literal.index('Definition Cert215'):].replace('Definition Cert215', 'Definition Cert215Literal', 1)
    audit = compact + '\n' + literal_decl + '''

Theorem certificate_exact : Cert215 = Cert215Literal.
Proof. reflexivity. Qed.

Print Assumptions certificate_exact.
'''
    audit_path = args.out / 'Cert215CompactAudit.v'
    audit_path.write_text(audit)
    receipt = {
        'schema': 'k215-rocq-path-compaction-v1',
        'snapshot': 'b6c7087477e51c017003bd729e712c8969733223',
        'source': 'Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Cert215Offsets.v',
        'source_sha256': hashlib.sha256(literal.encode()).hexdigest(),
        'compact_sha256': hashlib.sha256(compact.encode()).hexdigest(),
        'before_bytes': len(literal.encode()),
        'after_bytes': len(compact.encode()),
        'saved_bytes': len(literal.encode()) - len(compact.encode()),
        'entries': len(entries),
        'all_paths_exactly_reconstructed': True,
        'all_offsets_and_successor_indices_preserved': True,
        'full_endpoint_rebuilt': False,
        'kernel_audit': {'status': 'not_requested'}
    }
    if args.coqc:
        proc = subprocess.run([str(args.coqc.resolve()), audit_path.name],
                              cwd=args.out, capture_output=True, text=True)
        (args.out / 'compact_paths_kernel.log').write_text(proc.stdout + proc.stderr)
        version = subprocess.check_output([str(args.coqc.resolve()), '--version'], text=True).strip()
        receipt['kernel_audit'] = dict(status='PASS' if proc.returncode == 0 else 'FAIL',
            compiler=version, returncode=proc.returncode,
            stdout=proc.stdout, stderr=proc.stderr,
            audit_sha256=hashlib.sha256(audit.encode()).hexdigest())
        (args.out / 'compact_paths_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        assert proc.returncode == 0, proc.stdout + proc.stderr
        if args.coqchk:
            chk = subprocess.run([str(args.coqchk.resolve()), '-silent', 'Cert215CompactAudit'],
                                 cwd=args.out, capture_output=True, text=True)
            (args.out / 'compact_paths_coqchk.log').write_text(chk.stdout + chk.stderr)
            receipt['kernel_audit']['coqchk_returncode'] = chk.returncode
            receipt['kernel_audit']['coqchk_status'] = 'PASS' if chk.returncode == 0 else 'FAIL'
            assert chk.returncode == 0, chk.stdout + chk.stderr
    (args.out / 'compact_paths_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
