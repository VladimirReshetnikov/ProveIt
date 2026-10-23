#!/usr/bin/env python3
"""Read-only census and deterministic producer of a concrete Coq support witness.

No Python result is used as a proof premise. Support215217.v contains the full
sparse tables and an independently kernel-checked finite agreement statement.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

PIN = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
BASE = 'Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension'
STATES = [0, 1, 2, 3, 16, 22, 25, 32, 33, 36, 40, 48, 51, 54, 55, 60, 64, 66, 74, 94, 97, 113, 198]
ROWS = [(q, b) for q in STATES for b in [0, 1] if not (b == 0 and q in [113, 198])]
VARIANTS = [215, 217, 218, 221, 225, 226, 227, 229]
SHARED = ['Zip', 'Runtime230Core', 'Tape230Blocks', 'Tape230Carry', 'Interpreter230Sites']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def parse(p):
    ans = {}
    for line in p.read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, n = line.split()
            key = int(q), int(b)
            assert key not in ans
            ans[key] = int(w), d, int(n)
    return ans

def without_comments(s):
    # Coq comments may be nested: use a small scanner, not a non-greedy regex.
    result, depth, i = [], 0, 0
    while i < len(s):
        if s[i:i+2] == '(*':
            depth += 1
            i += 2
        elif depth and s[i:i+2] == '*)':
            depth -= 1
            i += 2
        else:
            if not depth:
                result.append(s[i])
            i += 1
    assert depth == 0
    return ''.join(result)

def normalized_body(p):
    # Only comments, variant namespace spelling, and line-edge whitespace.
    s = re.sub(r'\bK\d+F\b', 'KVF', without_comments(p.read_text()))
    return '\n'.join(line.strip() for line in s.splitlines() if line.strip())

def emit_table(name, table):
    def row(q, b):
        v = table.get((q, b))
        if v is None:
            return 'None'
        w, d, n = v
        return f'Some ({str(bool(w)).lower()}, {str(d == "R").lower()}, {n})'
    lines = [f'Definition {name} : list (option transition * option transition) := [']
    lines += [f'  ({row(q, 0)}, {row(q, 1)})' + (';' if q < 229 else '') for q in range(230)]
    return '\n'.join(lines + ['].', ''])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', required=True, type=Path)
    ap.add_argument('--out', type=Path, default=Path(__file__).resolve().parent)
    args = ap.parse_args()
    root, out = args.repo.resolve(), args.out.resolve()
    ext = root / BASE
    out.mkdir(parents=True, exist_ok=True)
    head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    if head != PIN:
        raise SystemExit(f'Expected {PIN}, got {head}; review pin before rerunning.')
    inputs, tables = {}, {}
    for v in VARIANTS:
        p = ext / f'inputs/{v}/' / ('k229_k230labels.tm' if v == 229 else 'table_k230labels.tm')
        inputs[str(v)] = {'path': str(p.relative_to(root)), 'sha256': sha(p)}
        tables[v] = parse(p)
    base = tables[215]
    comparisons = []
    for v in VARIANTS[1:]:
        table = tables[v]
        different = [[q, b, base.get((q, b)), table.get((q, b))]
                     for q, b in sorted(set(base) | set(table))
                     if base.get((q, b)) != table.get((q, b))]
        comparisons.append({'other': v, 'different_rows': len(different),
                            'box_rows_count': len(ROWS),
                            'different_box_rows': [list(r) for r in ROWS if base.get(r) != table.get(r)],
                            'increment_tail_198_0': table.get((198, 0)),
                            'different_rows_detail': different})
    duplicates = []
    for name in SHARED:
        records, groups = [], {}
        for v in VARIANTS:
            p = ext / f'coq/{v}/{name}.v'
            body = normalized_body(p)
            h = hashlib.sha256(body.encode()).hexdigest()
            groups.setdefault(h, []).append(v)
            records.append({'variant': v, 'bytes': p.stat().st_size,
                            'lines': len(p.read_text().splitlines()), 'sha256': sha(p)})
        duplicates.append({'module': name, 'total_bytes': sum(r['bytes'] for r in records),
                           'groups_after_normalization': list(groups.values()), 'files': records})
    census = {'pin': PIN, 'inputs': inputs, 'box_states': STATES, 'box_rows': ROWS,
              'box_rows_origin': 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTape.lean',
              'comparisons': comparisons, 'shared_module_census': duplicates,
              'normalization': 'delete nested Coq comments; replace K<digits>F namespace only; strip line-edge whitespace and blank lines',
              'total_physical_bytes_five_modules': sum(r['total_bytes'] for r in duplicates),
              'disclaimer': 'Source duplication census and finite row equality; not a new endpoint or runtime timing measurement.'}
    (out / 'runtime_audit.json').write_text(json.dumps(census, indent=2) + '\n')
    text = '''(** Generated by audit_runtime.py from the full sparse K215/K217 tables.
    Commit: ''' + PIN + '''.
    Both table hashes are recorded in runtime_audit.json. The tables differ;
    only the stated register-engine support is shared. This finite witness
    does not assert that a particular symbolic program uses only that support. *)
From Coq Require Import List Bool Arith.
Require Import OracleFootprint.
Import ListNotations.
Set Implicit Arguments.

Definition transition := (bool * bool * nat)%type.
Definition key := (nat * bool)%type.
Definition answer := option transition.
Definition table_lookup (table : list (answer * answer)) (r : key) : answer :=
  let pair := nth (fst r) table (None, None) in
  if snd r then snd pair else fst pair.

'''
    text += emit_table('table215', tables[215]) + emit_table('table217', tables[217])
    text += '''Definition M215 : key -> answer := table_lookup table215.
Definition M217 : key -> answer := table_lookup table217.
Definition box_rows : list key := [
'''
    text += ';\n'.join(f'  ({q}, {str(bool(b)).lower()})' for q,b in ROWS)
    text += r'''
].
Definition support : list key := box_rows ++ [(198, false)].

Definition answer_dec : forall x y : answer, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Definition answer_eqb (x y : answer) : bool := if answer_dec x y then true else false.
Lemma answer_eqb_sound x y : answer_eqb x y = true -> x = y.
Proof. unfold answer_eqb. destruct (answer_dec x y); intros H; [assumption|discriminate]. Qed.

Lemma box_rows_length : length box_rows = 44.
Proof. reflexivity. Qed.
Lemma support_length : length support = 45.
Proof. reflexivity. Qed.

Lemma support_check : check_support answer_eqb M215 M217 support = true.
Proof. vm_compute. reflexivity. Qed.

Theorem support_agreement : agrees_on M215 M217 support.
Proof. exact (check_support_sound answer_eqb answer_eqb_sound M215 M217 support support_check). Qed.

Lemma K215_increment_bypass : M215 (198, false) = Some (true, false, 40).
Proof. reflexivity. Qed.
Lemma K217_increment_bypass : M217 (198, false) = Some (true, false, 40).
Proof. reflexivity. Qed.

Lemma tables_really_differ : M215 (11, true) <> M217 (11, true).
Proof. discriminate. Qed.

(** A missing row is part of the observations, rather than an unrecorded event. *)
Lemma rejected_missing_row : check_support answer_eqb M215 M217 [(183, false)] = false.
Proof. vm_compute. reflexivity. Qed.

Theorem supported_computation_reuse (C : Type)
    (p : query_tree key answer (option (C * bool))) :
  (forall r, In r (reads M215 p) -> In r support) ->
  value M217 p = value M215 p /\ reads M217 p = reads M215 p.
Proof.
  intro H. apply static_support_transport with (support := support).
  - exact H.
  - exact support_agreement.
Qed.

Print Assumptions support_agreement.
Print Assumptions supported_computation_reuse.
Print Assumptions rejected_missing_row.
'''
    (out / 'Support215217.v').write_text(text)
    print(json.dumps({'pin': head, 'files': ['runtime_audit.json', 'Support215217.v'],
                      'shared_bytes': census['total_physical_bytes_five_modules'],
                      'table_differences': [{k:r[k] for k in ['other','different_rows','different_box_rows']}
                                            for r in comparisons]}, indent=2))

if __name__ == '__main__':
    main()
