#!/usr/bin/env python3
"""Render inferred Lean MSB-sentinel path codes as untrusted Rocq data."""
from pathlib import Path
import json
root=Path(__file__).resolve().parent
rows=json.loads((root/'entries.json').read_text())
assert len(rows)==1426
assert all(isinstance(v,int) for row in rows for v in row)
assert all(a>0 and b>0 and 0<=j<len(rows) and 0<=k<len(rows) for a,b,j,k in rows)
header="""(** The certificate inferred by Lean from the two literal source trees.
    Positive codes have a high sentinel and MSB-first path bits.
    Only semantic checker acceptance gives this untrusted data meaning. *)
From Coq Require Import List PArith NArith.
From K230P Require Import Bisim230.
Require Import PathCodec.
Import ListNotations.

Definition auto_packed : list packed_entry := [
"""
body=';\n'.join('  (%s%%positive,%s%%positive,%d%%N,%d%%N)' % tuple(row) for row in rows)
footer="""].

Definition auto_expand (x : packed_entry) : entry :=
  let '(a,b,j,k) := x in (rev (decode_path a),rev (decode_path b),j,k).

Definition auto_certificate : list entry := Eval vm_compute in
  map auto_expand auto_packed.

Theorem auto_certificate_entries : length auto_certificate = 1426.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions auto_certificate_entries.
"""
(root/'AutoCert215.v').write_text(header+body+footer)
