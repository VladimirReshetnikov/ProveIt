#!/usr/bin/env python3
"""Construct the direct compiler overlay; never modify the input checkout."""
from pathlib import Path
import argparse, hashlib, json, difflib

ap = argparse.ArgumentParser()
ap.add_argument('--repo', type=Path, required=True)
ap.add_argument('--out', type=Path, required=True)
a = ap.parse_args()
repo, out = a.repo.resolve(), a.out.resolve()
base = Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
prod = base / 'rocq/rocq-extension/coq/215'
templates = base / 'rocqperm'
core = '''(** ** Compile directly into the algebra of block contracts. *)
Definition Compilable (X : nat) : Prop := exists L, blk X L.

Lemma compilable_dom_imp : DomImp Compilable.
Proof.
  constructor.
  - exists DISCARD. exact blk_true.
  - intros a b [LI HI] [LA HA].
    exists (mpb b LA LI). exact (blk_mp a b LA LI HA HI).
  - intros a b c u Hu. exists (leaf 8 a b c u). now apply blk_r8.
Qed.

Lemma compile_direct X : thm222 X -> exists L, blk X L.
Proof.
  induction 1 as [| t b _ [LA HA] _ [LI HI] | a hh _ [L HL]
                  | a b | a b c | a b c | a b c | a b c | a b | a b c | a b c u | a b c H1 H2].
  - exists DISCARD. exact blk_true.
  - exists (mpb b LA LI). exact (blk_mp t b LA LI HA HI).
  - exists (genb a L). exact (blk_gen a hh L HL).
  - exists (leaf 1 a b 0 0). apply blk_r1.
  - exists (leaf 2 a b c 0). apply blk_r2.
  - exists (leaf 3 a b c 0). apply blk_r3.
  - exists (leaf 4 a b c 0). apply blk_r4.
  - exists (leaf 5 a b c 0). apply blk_r5.
  - exists (leaf 6 a 0 b 0). apply blk_r6.
  - exists (leaf 7 a b c 0). apply blk_r7.
  - exact (rho8_all Compilable compilable_dom_imp a b c u).
  - exists (leafB a b c). now apply blk_bundle.
Qed.
'''

def comp(text):
    text = text.replace('a derivation of the dominated calculus [thmDom]\n    compiles to a command list.', 'a derivation of [thm222] compiles directly to a command list\n    by interpreting dominated implication in block contracts.')
    text = text.replace('Codes222 EnumPerm Thm222 ThmDom.', 'Codes222 EnumPerm Thm222 DomRho8.')
    start = text.index('(** ** Compilation of derivations of the dominated calculus *)')
    end = text.index('(** ** The whole program halts from every retained state *)', start)
    text = text[:start] + core + '\n' + text[end:]
    text = text.replace('compile 1 (thmDom_of_thm222 1 H)', 'compile_direct 1 H')
    assert 'ThmDom' not in text and 'thmDom_of_thm222' not in text
    return text

def seed(text):
    text = text.replace('Codes222 Thm222 ThmDom EnumPerm', 'Codes222 Thm222 EnumPerm')
    text = text.replace('compile 1 (thmDom_of_thm222 1 H)', 'compile_direct 1 H')
    return text

changes = {}
for name, transform in [('L1_CompPerm.v', comp), ('SeedPerm.v', seed)]:
    path = templates / name
    changes[path] = transform((repo / path).read_text())
    digest = hashlib.sha256(changes[path].encode()).hexdigest()
    rendered = changes[path].replace('From NS Require', 'From K215F Require')
    changes[prod / name] = f'(** k225-formal/rocqperm/{name} (SHA256 {digest}) under namespace K215F. *)\n' + rendered

compat = '''(** Optional compatibility client; excluded from the K215 endpoint spine.
    The old compiler statement is available as CompilerDomCompat.compile.
    The old fully qualified L1_CompPerm.compile name is intentionally retired. *)
From K215F Require Import Thm222 ThmDom L1_CompPerm.

Lemma compile X : thmDom X -> exists L, blk X L.
Proof. intro H. apply compile_direct. now apply thm222_of_thmDom. Qed.
Print Assumptions compile.
'''
(out / 'compat').mkdir(parents=True, exist_ok=True)
(out / 'compat' / 'CompilerDomCompat.v').write_text(compat)
old_compat = out / 'overlay' / prod / 'CompilerDomCompat.v'
if old_compat.exists(): old_compat.unlink()
manifest_path = base / 'rocq/rocq-extension/manifest.json'
manifest = (repo / manifest_path).read_text()
for name in ['L1_CompPerm.v', 'SeedPerm.v']:
    old_hash = hashlib.sha256((repo / prod / name).read_bytes()).hexdigest()
    new_hash = hashlib.sha256(changes[prod / name].encode()).hexdigest()
    old_entry = f'"coq/215/{name}": "{old_hash}"'
    new_entry = f'"coq/215/{name}": "{new_hash}"'
    assert manifest.count(old_entry) == 1
    manifest = manifest.replace(old_entry, new_entry)
changes[manifest_path] = manifest
diff = []
records = []
for rel, new in changes.items():
    oldpath = repo / rel
    old = oldpath.read_text() if oldpath.exists() else ''
    dest = out / 'overlay' / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(new)
    diff.extend(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile='a/'+str(rel) if old else '/dev/null', tofile='b/'+str(rel)))
    records.append({'path': str(rel), 'before_bytes': len(old.encode()), 'after_bytes': len(new.encode()), 'before_lines': len(old.splitlines()), 'after_lines': len(new.splitlines()), 'sha256': hashlib.sha256(new.encode()).hexdigest()})
(out / 'compiler-fusion.patch').write_text(''.join(diff))
(out / 'metrics.json').write_text(json.dumps({'baseline': '6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95', 'files': records, 'optional_compatibility': {'bytes': len(compat.encode()), 'lines': len(compat.splitlines())}, 'endpoint_source_saving': {'lines':59, 'bytes':1565, 'modules':1}, 'note': 'Current DomRho8 is unchanged. ThmDom remains available for optional compatibility; its 70 lines leave the endpoint closure. Endpoint counts are source-closure predictions, not a rebuilt endpoint claim.'}, indent=2)+'\n')
print(json.dumps(records, indent=2))
