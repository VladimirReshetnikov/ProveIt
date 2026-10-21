#!/usr/bin/env python3
"""Losslessly pack the pinned K215 certificate; an independent Coq equality checks it.

Usage: python3 pack_certificate.py /absolute/path/to/Cert215Offsets.v
This generator is untrusted; Cert215Exact.v proves exact expansion equality.
"""
from pathlib import Path
import hashlib, json, re, sys

root = Path(__file__).resolve().parent
source = Path(sys.argv[1])
raw = source.read_bytes()
expected = '32197f6f31bd3c7c7bf5fb94af0e721434f1238d64a64a715b8c9d2cbdd4e728'
assert hashlib.sha256(raw).hexdigest() == expected, 'Unexpected source version'
text = raw.decode()
pattern = re.compile(r'\(\[([a-z;]*)\], \[([a-z;]*)\], ([-0-9]+)%Z, ([0-9]+)%N, ([0-9]+)%N\)')
rows = pattern.findall(text)
assert rows, 'No certificate rows found'
# Every nontrivial line must match, so omitted/unparsed rows are not silently lost.
body = text.split(':= [', 1)[1].rsplit('].', 1)[0]
assert re.sub(r'[;\s]', '', pattern.sub('', body)) == '', 'Unparsed certificate data'
def bits(s):
    ans = [] if not s else s.split(';')
    assert all(x in ('false','true') for x in ans)
    return [x == 'true' for x in ans]
def encode(bs):
    p = 1
    for b in reversed(bs): p = 2*p + b
    return p
packed = []
max_lengths = [0, 0]
for a,b,z,j,k in rows:
    assert int(z) == 0, 'The zero-offset specialization is inapplicable'
    ab,bb = bits(a),bits(b)
    for i,x in enumerate((ab,bb)):max_lengths[i] = max(max_lengths[i],len(x))
    packed.append(f'  ({encode(ab)}%positive,{encode(bb)}%positive,{j}%N,{k}%N)')
header = '''(** Generated lossless binary-path presentation of the existing K215 certificate.
    Every entry has offset zero.  See Cert215Exact.v for kernel-checked equality. *)
From Coq Require Import List PArith NArith ZArith.
Require Import PathCodec.
Import ListNotations.
Definition packed215 : list packed_entry := [
'''
result = header + ';\n'.join(packed) + '\n].\nDefinition Cert215 := Eval vm_compute in map expand_entry packed215.\nDefinition Plain215 := Eval vm_compute in map expand_plain packed215.\n'
(root/'Cert215Compact.v').write_text(result)
(root/'OriginalCert215.v').write_bytes(raw)
(root/'Cert215Exact.v').write_text('''(** Exact equality of all ordered certificate entries, not a hash-only check. *)
From Coq Require Import List.
Require Import OriginalCert215 Cert215Compact.
Theorem certificate_exact : Cert215Compact.Cert215 = OriginalCert215.Cert215.
Proof. vm_compute. reflexivity. Qed.
Theorem certificate_length : length Cert215Compact.Cert215 = 2240.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions certificate_exact.
Print Assumptions certificate_length.
''')
metrics = dict(original_sha256=hashlib.sha256(raw).hexdigest(),
               original_bytes=len(raw), compact_bytes=len(result.encode()),
               codec_bytes=(root/'PathCodec.v').stat().st_size,
               entries=len(rows), nonzero_offsets=0, maximum_path_lengths=max_lengths,
               compact_sha256=hashlib.sha256(result.encode()).hexdigest())
metrics['replacement_plus_codec_bytes']=metrics['compact_bytes']+metrics['codec_bytes']
metrics['source_reduction_percent']=100*(1-metrics['replacement_plus_codec_bytes']/len(raw))
metrics['original_lines']=len(text.splitlines())
metrics['compact_lines']=len(result.splitlines())
metrics['codec_lines']=len((root/'PathCodec.v').read_text().splitlines())
metrics['plain_symmetry_bytes']=(root/'BisimMirror.v').stat().st_size
metrics['plain_symmetry_lines']=len((root/'BisimMirror.v').read_text().splitlines())
metrics['omitted_offset_layer_bytes']=(root/'deps/K215F/OffsetBisim230.v').stat().st_size
metrics['omitted_offset_layer_lines']=len((root/'deps/K215F/OffsetBisim230.v').read_text().splitlines())
(root/'certificate_metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
