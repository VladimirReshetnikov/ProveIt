#!/usr/bin/env python3
"""Render the inherited normalized certificate as compact, untrusted Rocq data."""
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parent
source = ROOT / 'normalized_certificate.json'
data = json.loads(source.read_text())
rows = data['entries']
assert len(rows) == 1426
assert all(int(a) > 0 and int(b) > 0 and 0 <= j < len(rows) and 0 <= k < len(rows)
           for a, b, j, k in rows)
header = '''(** The inherited 1,426-entry normalized K215 certificate.
    Numerals have a high sentinel bit and carry paths from most to least
    significant bit; the reversed positive decoder preserves every bit.
    This data is untrusted until the actual normalized checker accepts it. *)
From Coq Require Import List PArith NArith.
From K230P Require Import Bisim230.
Require Import PathCodec.
Import ListNotations.

Definition normalized_packed : list packed_entry := [
'''
body = ';\n'.join('  (%s%%positive,%s%%positive,%d%%N,%d%%N)' % tuple(row) for row in rows)
footer = ''']. 

Definition expand_msb (x : packed_entry) : entry :=
  let '(a,b,j,k) := x in (rev (decode_path a),rev (decode_path b),j,k).

Definition normalized_certificate : list entry := Eval vm_compute in
  map expand_msb normalized_packed.

Theorem certificate_entries : length normalized_certificate = 1426.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions certificate_entries.
'''
(ROOT / 'NormalizedCert215.v').write_text(header + body + footer)
print(json.dumps({'input_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                  'entries': len(rows), 'output_bytes': len((header + body + footer).encode())}, indent=2))
