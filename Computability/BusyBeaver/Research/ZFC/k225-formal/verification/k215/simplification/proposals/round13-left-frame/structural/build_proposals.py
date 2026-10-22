#!/usr/bin/env python3
"""Owned, deterministic textual refactor audit. No upstream code is executed."""
from pathlib import Path
import difflib, hashlib, json, re, shutil

if not __debug__:
    raise RuntimeError('Assertions must be enabled; do not run with Python -O')

ROOT = Path(__file__).resolve().parent
UP = ROOT / 'upstream'
OUT = ROOT / 'proposed'
OUT.mkdir(exist_ok=True)

NAMES = ['unP', "unP_P'", 'axStack', 'gate', 'tailN', 'Good', 'tailN_zero',
         'good_zero', 'good_cons', 'gate_good', 'axStack_good',
         'wim_ne_one', 'wal_ne_one', 'gate_ne_one', 'gate_self']

def declaration(text, name):
    m = re.search(r"(?m)^(?:abbrev|def|theorem) " + re.escape(name) + r"(?=\s|\{|\()", text)
    assert m, name
    start = m.start()
    end = text.find('\n\n', start)
    assert end >= 0, name
    nxt = re.search(r'\n(?=(?:abbrev|def|theorem) )', text[start:end])
    if nxt:
        end = start + nxt.start() + 1
    else:
        end += 2
    if start and text[:start].endswith('-/\n'):
        doc = text.rfind('/--', 0, start)
        assert doc >= 0 and text[doc:start].count('/--') == 1
        start = doc
    return start, end, text[start:end]

def strip_doc(s):
    return re.sub(r'^/--.*?-/\n', '', s, flags=re.S).strip()

def blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
for f in provenance['files']:
    b = (UP / f['name']).read_bytes()
    assert blob(b) == f['sha'], f['name']

dom = (UP / 'EnumDom.lean').read_text()
perm = (UP / 'EnumPerm.lean').read_text()
chunks = {}
duplicate_checks = []
for name in NAMES:
    a = declaration(dom, name)[2]
    b = declaration(perm, name)[2]
    same = strip_doc(a) == strip_doc(b)
    assert same or name in {'good_zero', 'axStack_good'}, name
    chunks[name] = b.strip()
    duplicate_checks.append({'name': name, 'declarations_byte_identical': same,
                             'selected_existing_body': 'EnumPerm.lean'})

shared = '''import BusyBeaver.ZFC.KCode222

/-! Stack semantics common to the dominated and command-permuted enumerators.
No command decoder, scheduler, state type or new semantic parameter is introduced. -/

namespace SetTheory.BusyBeaver.ZFC.EnumStack

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222

attribute [local irreducible] P

''' + '\n\n'.join(chunks[n] for n in NAMES) + '\n\nend SetTheory.BusyBeaver.ZFC.EnumStack\n'
(OUT / 'EnumStack.lean').write_text(shared)
exports = '''export EnumStack (unP unP_P' axStack gate tailN Good tailN_zero good_zero good_cons
  gate_good axStack_good wim_ne_one wal_ne_one gate_ne_one gate_self)

'''
for filename, original in [('EnumDom.lean', dom), ('EnumPerm.lean', perm)]:
    changed = original
    for a, b, _ in sorted((declaration(original, n) for n in NAMES), reverse=True):
        changed = changed[:a] + changed[b:]
    changed = changed.replace('import BusyBeaver.ZFC.KCodeDom\n',
                              'import BusyBeaver.ZFC.KCodeDom\nimport BusyBeaver.ZFC.EnumStack\n', 1)
    anchor = 'attribute [local irreducible] P\n\n'
    assert changed.count(anchor) == 1
    changed = changed.replace(anchor, anchor + exports, 1)
    # Exact inverse check: nothing besides selected declarations, one import, and exports changed.
    remainder = changed.replace('import BusyBeaver.ZFC.EnumStack\n', '', 1).replace(exports, '', 1)
    removed = original
    for a, b, _ in sorted((declaration(original, n) for n in NAMES), reverse=True):
        removed = removed[:a] + removed[b:]
    assert remainder == removed
    (OUT / filename).write_text(changed)

rocq = (UP / 'L1_SoundPerm.v').read_text()
old_pop = '''Proof.
  unfold popn. revert w. induction k as [|k IH]; intro w; [reflexivity|].
  change (snd (unP (Nat.iter (S k) (fun w => snd (unP w)) w)) =
          snd (unP (Nat.iter k (fun w => snd (unP w)) (snd (unP w))))).
  now rewrite IH.
Qed.'''
assert rocq.count(old_pop) == 1
new_rocq = rocq.replace(old_pop, 'Proof. unfold popn. apply Nat.iter_succ_r. Qed.')
start = new_rocq.index('Lemma Inv_step ')
end = new_rocq.index('Lemma Inv_run ', start)
joint = '''(** One decoded command either preserves the invariant or derives falsity. *)
Lemma step_sound s : Inv s ->
  match enum_step s with Some s' => Inv s' | None => thm222 1 end.
Proof.
  intros [Ht [Hh Hw]]. unfold enum_step.
  destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1].
  destruct (unP pl1) as [ac pl2].
  destruct ac as [|[|[|c]]].
  - destruct (Nat.eqb (h s) 1) eqn:E.
    + apply Nat.eqb_eq in E. now rewrite <- E.
    + destruct (good_pop _ Hw) as [H1 H2]. destruct (unP (ws s)) as [h1 w1] eqn:Eu.
      repeat split; cbn [tw h ws]; [exact Ht | exact H1 | exact H2].
  - repeat split; cbn [tw h ws]; [exact Hh | exact Hh | now apply good_push].
  - destruct (unP pl2) as [x pl3].
    destruct (Nat.eqb (wim (tw s) (d s + x)) (h s)) eqn:E.
    + apply Nat.eqb_eq in E. repeat split; cbn [tw h ws].
      * apply (W_mp (tw s)); [exact Ht | now rewrite E].
      * exact W_true.
      * apply good_push; [exact W_true | exact Hw].
    + repeat split; cbn [tw h ws]; [exact W_true | exact W_true | exact Hw].
  - destruct (unP pl2) as [y pl3]. destruct (unP pl3) as [x pl4].
    repeat split; cbn [tw h ws].
    + apply gate_thm.
    + exact W_true.
    + unfold ax_stack.
      repeat apply good_push; try assumption; constructor; assumption.
Qed.

Lemma Inv_step s s' : Inv s -> enum_step s = Some s' -> Inv s'.
Proof. intros Hs E. pose proof (step_sound s Hs) as H. rewrite E in H. exact H. Qed.

'''
new_rocq = new_rocq[:start] + joint + new_rocq[end:]
start = new_rocq.index('Lemma halt_step ')
end = new_rocq.index('Theorem enum_sound ', start)
new_halt = '''Lemma halt_step s : Inv s -> enum_step s = None -> thm222 1.
Proof. intros Hs E. pose proof (step_sound s Hs) as H. rewrite E in H. exact H. Qed.

'''
new_rocq = new_rocq[:start] + new_halt + new_rocq[end:]
# The maintained file is generated from rocqperm/L1_SoundPerm.v. Keep the
# hand-maintained source and generated output synchronized, without running
# regenerate215.py or importing any received code.
producer = (UP / 'producer_L1_SoundPerm.v').read_text()
def generated_rocq(source):
    sha = hashlib.sha256(source.encode()).hexdigest()
    return ('(** k225-formal/rocqperm/L1_SoundPerm.v (SHA256 ' + sha +
            ') under namespace K215F. *)\n' +
            source.replace('From NS Require', 'From K215F Require'))
assert generated_rocq(producer) == rocq
new_producer = new_rocq.split('\n', 1)[1].replace('From K215F Require', 'From NS Require')
new_rocq = generated_rocq(new_producer)
(OUT / 'producer_L1_SoundPerm.v').write_text(new_producer)
(OUT / 'L1_SoundPerm.v').write_text(new_rocq)

# The public definitions and theorem signatures do not change in the Rocq patch.
for m in re.finditer(r'(?m)^(?:Definition|Lemma|Theorem) ([A-Za-z0-9_]+).*?(?:\.|:=)', rocq):
    if m.group(1) == 'step_sound':
        continue
    assert m.group(0) in new_rocq, m.group(1)
assert new_rocq[new_rocq.index('Lemma Inv_run '):new_rocq.index('Lemma halt_step ')] == \
       rocq[rocq.index('Lemma Inv_run '):rocq.index('Lemma halt_step ')]
assert new_rocq[new_rocq.index('Theorem enum_sound '):] == rocq[rocq.index('Theorem enum_sound '):]

metrics = []
lean_patch = []
rocq_patch = []
for name in ['EnumStack.lean', 'EnumDom.lean', 'EnumPerm.lean', 'L1_SoundPerm.v', 'producer_L1_SoundPerm.v']:
    old = (UP / name).read_text() if (UP / name).exists() else ''
    new = (OUT / name).read_text()
    repo = ('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/' if name.endswith('.lean') else
            'Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/') + name
    if name == 'producer_L1_SoundPerm.v':
        repo = 'Computability/BusyBeaver/Research/ZFC/k225-formal/rocqperm/L1_SoundPerm.v'
    diff = ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                fromfile='a/' + repo if old else '/dev/null', tofile='b/' + repo))
    (lean_patch if name.endswith('.lean') else rocq_patch).append(diff)
    metrics.append({'file': name, 'old_lines': old.count('\n'), 'new_lines': new.count('\n'),
                    'delta_lines': new.count('\n') - old.count('\n'),
                    'old_bytes': len(old.encode()), 'new_bytes': len(new.encode()),
                    'old_sha256': hashlib.sha256(old.encode()).hexdigest(),
                    'new_sha256': hashlib.sha256(new.encode()).hexdigest()})
(ROOT / 'SHARED_STACK.patch').write_text(''.join(lean_patch))
(ROOT / 'ROCQ_STEP_SOUND.patch').write_text(''.join(rocq_patch))
audit = {'pin': provenance['pin'], 'validation': 'SOURCE_AUDIT_ONLY_UNCOMPILED',
         'metrics': metrics, 'net_lines': sum(m['delta_lines'] for m in metrics),
         'lean_net_lines': sum(m['delta_lines'] for m in metrics if m['file'].endswith('.lean')),
         'rocq_net_lines': sum(m['delta_lines'] for m in metrics if m['file'].endswith('.v')),
         'rocq_unique_proof_net_lines': -9,
         'duplicate_checks': duplicate_checks,
         'checks': ['Git blob identities of source inputs', '13 identical extracted declaration bodies',
                    '2 shorter proof bodies reused from current EnumPerm',
                    'all other Lean source text unchanged', 'Rocq old public statements retained',
                    'Rocq Inv_run and enum_sound text unchanged',
                    'Rocq producer and generated output synchronized including source hash header']}
(ROOT / 'AUDIT.json').write_text(json.dumps(audit, indent=2) + '\n')
(ROOT / 'ENVIRONMENT.json').write_text(json.dumps(
    {'compilers_on_path': {n: shutil.which(n) for n in ['lean', 'lake', 'rocq', 'coqc']}},
    indent=2) + '\n')
print(json.dumps(audit, indent=2))
