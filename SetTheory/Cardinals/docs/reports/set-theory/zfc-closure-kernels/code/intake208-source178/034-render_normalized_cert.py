#!/usr/bin/env python3
"""Render the previously delivered shared JSON certificate for Rocq.
The renderer is untrusted: NormalizedSource215.v checks its entire output.
"""
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'normalized_certificate.json'
doc=json.loads(SOURCE.read_text())
assert doc['schema']=='K215-normalized-source-bisim-v1'
assert len(doc['entries'])==1426
# JSON uses most-significant-bit first, while PathCodec uses recursive head bits.
def convert(value):
    bits=bin(int(value))[3:]
    return int('1'+bits[::-1],2)
lines=['(** Derived from the exact normalized_certificate.json of incoming packet 2. *)',
       'From Coq Require Import List PArith NArith.',
       'Require Import PathCodec.', 'Import ListNotations.',
       'Definition packed_normalized215 : list packed_entry := [']
lines += ['  (%d%%positive,%d%%positive,%d%%N,%d%%N)%s' % (convert(a),convert(b),j,k,';' if i+1<len(doc['entries']) else '') for i,(a,b,j,k) in enumerate(doc['entries'])]
lines += ['].','Definition Normalized215 : list plain_entry :=',
          '  Eval vm_compute in map expand_plain packed_normalized215.',
          'Lemma normalized215_length : length Normalized215 = 1426.',
          'Proof. reflexivity. Qed.']
(ROOT/'NormalizedCert215.v').write_text('\n'.join(lines)+'\n')
print(json.dumps({'json_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'entries':len(doc['entries']),'rocq_bytes':(ROOT/'NormalizedCert215.v').stat().st_size},indent=2))
