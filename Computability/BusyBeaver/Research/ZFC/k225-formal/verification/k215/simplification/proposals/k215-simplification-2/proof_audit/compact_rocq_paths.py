#!/usr/bin/env python3
"""Losslessly pack the 2,240-entry Rocq K215 path certificate.

No theorem about the machine changes. Existing certificate_forward/backward
VM checks remain the validation gate. This script performs exact independent
Python roundtrip checks but does not claim to invoke Rocq.
Usage: python3 compact_rocq_paths.py INPUT.v OUTPUT_DIRECTORY
"""
import argparse
import hashlib
import json
import re
from pathlib import Path


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


def pack(bits):
    # Sentinel 1 preserves all false bits, including both ends.
    return (1 << len(bits)) | sum(int(b) << i for i, b in enumerate(bits))


def unpack(number):
    assert number > 0
    bits = []
    while number != 1:
        bits.append(bool(number & 1))
        number >>= 1
    return tuple(bits)


def read_original(source):
    pat = r'\(\[([a-z;]*)\], \[([a-z;]*)\], (-?[0-9]+)%Z, ([0-9]+)%N, ([0-9]+)%N\)'
    def bits(field):
        if not field:
            return ()
        words = field.split(';')
        assert all(w in ('false', 'true') for w in words)
        return tuple(w == 'true' for w in words)
    result = [(bits(a), bits(b), int(z), int(j), int(k))
              for a,b,z,j,k in re.findall(pat,source)]
    assert len(result) == 2240, len(result)
    assert all(z == 0 for _,_,z,_,_ in result)
    assert all(0 <= j < len(result) and 0 <= k < len(result) for *_,j,k in result)
    return result


PRELUDE = '''(** Proposed exact compression of Cert215Offsets.v.
    The existing Source215 certificate checks must be rerun before adoption.
    Positive binary codes are read least-significant bit first; xH is the
    terminating sentinel, so all leading/trailing false bits are preserved. *)
From Coq Require Import List NArith ZArith.
Import ListNotations.

Fixpoint unpack_path (p : positive) : list bool :=
  match p with
  | xH => []
  | xO q => false :: unpack_path q
  | xI q => true :: unpack_path q
  end.

Fixpoint pack_path (P : list bool) : positive :=
  match P with
  | [] => xH
  | false :: Q => xO (pack_path Q)
  | true :: Q => xI (pack_path Q)
  end.

Lemma unpack_pack_path P : unpack_path (pack_path P) = P.
Proof.
  induction P as [|b P IH]; [reflexivity|].
  destruct b; cbn; now rewrite IH.
Qed.

Definition Cert215Packed : list (positive * positive * N * N) := [
'''

SUFFIX = '''\n].

Definition Cert215 : list (list bool * list bool * Z * N * N) :=
  map (fun '(a,b,j,k) => (unpack_path a, unpack_path b, 0%Z, j, k)) Cert215Packed.

Print Assumptions unpack_pack_path.
'''


def compact(source):
    entries = read_original(source)
    rows = [f'  ({pack(a)}%positive, {pack(b)}%positive, {j}%N, {k}%N)'
            for a,b,z,j,k in entries]
    result = PRELUDE+';\n'.join(rows)+SUFFIX
    # Independent parse of the actual emitted numeric file, not rows before rendering.
    decoded = [(unpack(int(a)), unpack(int(b)), 0, int(j), int(k))
               for a,b,j,k in re.findall(r'\(([0-9]+)%positive, ([0-9]+)%positive, ([0-9]+)%N, ([0-9]+)%N\)',result)]
    assert decoded == entries, 'certificate changed'
    metadata = {
        'status': 'PASS_EXACT_CERTIFICATE_ROUNDTRIP_NOT_KERNEL_COMPILED',
        'kernel_compiled': False,
        'input_sha256': sha(source), 'output_sha256': sha(result),
        'input_bytes': len(source.encode()), 'output_bytes': len(result.encode()),
        'saved_bytes': len(source.encode())-len(result.encode()),
        'entries': len(entries), 'nonzero_offsets': 0,
        'maximum_path_length': max(len(p) for a,b,*_ in entries for p in (a,b)),
        'empty_paths': sum(not p for a,b,*_ in entries for p in (a,b)),
        'checks': ['decode of every emitted packed entry equals original entry exactly',
                   'all 4480 path boundaries preserved by positive sentinel coding',
                   'all 2240 offsets are zero, exactly as in the original',
                   'all successor indices retained in original order'],
        'remaining_gate': 'Compile Cert215Offsets.v, then unchanged Source215.v and dependent endpoints; rerun recursive coqchk and compare assumptions.'
    }
    return result, metadata


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path);p.add_argument('output_directory',type=Path)
    args=p.parse_args()
    result,metadata=compact(args.input.read_text())
    args.output_directory.mkdir(parents=True,exist_ok=True)
    (args.output_directory/'Cert215Offsets.v').write_text(result)
    (args.output_directory/'compact_rocq_result.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata,indent=2))


if __name__=='__main__':
    main()
