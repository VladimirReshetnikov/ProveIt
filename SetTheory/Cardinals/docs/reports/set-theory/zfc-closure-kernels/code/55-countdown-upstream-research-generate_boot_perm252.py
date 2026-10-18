"""Generate literal table and full blank-prefix Lean data for permutation252.

Python supplies untrusted expected data only. Lean must separately check all
504 actions and every finite zipper chunk. No Lean build is launched here.
The candidate is a register-permuted public253 fold; it is distinct from the
older reduced-calculus Table252.lean. --check performs no writes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
DIRECTORY = ROOT / 'Computability/BusyBeaver/Research/ZFC/candidate-permutation252'
LEAN_DIRECTORY = ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
OLD_SHA256 = '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
PERMUTATION = [0, 3, 4, 5, 8, 1, 6, 2, 7]
LAST = 82552


def parse(raw):
    if hashlib.sha256(raw).hexdigest() != OLD_SHA256:
        raise ValueError('literal candidate differs from the selected frozen table')
    rows = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, move, nxt = line.split()
        key = int(q), int(bit)
        if key in rows or bit not in ('0', '1') or write not in ('0', '1') or move not in ('L', 'R'):
            raise ValueError('malformed or duplicated transition')
        rows[key] = int(write), move, int(nxt)
    states = [64] + [q for q in range(254) if q not in (5, 8, 64)]
    assert len(states) == 252
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert all(t in states or t == 254 for w, m, t in rows.values())
    mapping = {q: i for i, q in enumerate(states)} | {254: 252}
    canonical = {(mapping[q], b): (w, m, mapping[t]) for (q, b), (w, m, t) in rows.items()}
    assert len(canonical) == 504 and sum(t == 252 for w, m, t in canonical.values()) == 1
    return rows, states, mapping, canonical


def bits(values):
    return '[' + ', '.join('true' if b else 'false' for b in values) + ']'


def action(value, typed=False):
    w, m, t = value
    write = 'true' if w else 'false'
    move = 'right' if m == 'R' else 'left'
    if not typed:
        return f'({write}, .{move}, {t})'
    target = 'none' if t == 252 else f'some ⟨{t}, by decide⟩'
    return f'{{ write := {write}, move := .{move}, next := {target} }}'


def table_source(rows, canonical_sha):
    header = f'''import BusyBeaver.Core

/-!
Literal 252-state register-permutation candidate, separate from Table252.lean.

Mira-Cult designed the original254 machine and Jeff supplied its verification;
mira-emmy supplied the public253 reduction at0d544f2a2e3c18f12278441a74b7879f31cbe856.
This candidate additionally folds old5 into64 and permutes physical register
selectors by {PERMUTATION}. The search/generation is documented in Research/ZFC.
Frozen old-label SHA256: {OLD_SHA256}.
Canonical SHA256: {canonical_sha}.
Old start64 is canonical0; old halt254 is canonical252 and maps to none,
retaining its final write and head move. These are504 literal binary actions.
Finite table facts below do not prove runtime or consistency calibration.
-/
namespace SetTheory.BusyBeaver.ZFC
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
abbrev RawActionPerm252 := Bool × Move × Nat

def rawTablePerm252 : Array (RawActionPerm252 × RawActionPerm252) := #[
'''
    lines = []
    for q in range(252):
        comma = ',' if q < 251 else ''
        lines.append(f'  ({action(rows[q, 0])}, {action(rows[q, 1])}){comma} -- {q}')
    first = action(rows[0, 0], True)
    footer = f'''
]

theorem rawTablePerm252_size : rawTablePerm252.size = 252 := by decide

theorem rawTablePerm252_transition_count :
    (rawTablePerm252.toList.flatMap (fun row => [row.1, row.2])).length = 504 := by decide

theorem rawTablePerm252_targets_bounded :
    rawTablePerm252.toList.all (fun row =>
      decide (row.1.2.2 ≤ 252 ∧ row.2.2.2 ≤ 252)) = true := by decide

theorem rawTablePerm252_halt_edge_count :
    ((rawTablePerm252.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 252)).length = 1 := by decide

def rawActionPerm252 (state : Fin 252) (bit : Bool) : RawActionPerm252 :=
  let row := rawTablePerm252.getD state.val
    ((false, .right, 252), (false, .right, 252))
  if bit then row.2 else row.1

def actionPerm252 (state : Fin 252) (bit : Bool) : Action 252 :=
  let raw := rawActionPerm252 state bit
  {{ write := raw.1, move := raw.2.1,
    next := if h : raw.2.2 < 252 then some ⟨raw.2.2, h⟩ else none }}

def machinePerm252 : Machine 252 where
  transition := actionPerm252

def typedMachinePerm252 : TypedMachine (Fin 252) where
  transition state bit :=
    let a := actionPerm252 state bit
    {{ write := a.write, move := a.move, next := a.next }}

theorem machinePerm252_initial_action :
    machinePerm252.transition ⟨0, by decide⟩ false = {first} := by decide

#print axioms rawTablePerm252_size
#print axioms rawTablePerm252_transition_count
#print axioms rawTablePerm252_targets_bounded
#print axioms rawTablePerm252_halt_edge_count
#print axioms machinePerm252_initial_action
end SetTheory.BusyBeaver.ZFC
'''
    return header + '\n'.join(lines) + footer


def checkpoints(rows):
    depths = [12] * (LAST // 4096)
    remaining = LAST % 4096
    for depth in range(11, -1, -1):
        if remaining & (1 << depth):
            depths.append(depth)
    ends = [0]
    for depth in depths:
        ends.append(ends[-1] + (1 << depth))
    assert ends[-1] == LAST and len(depths) == 25
    targets = set(ends)
    q = head = 0
    left, right = [], []
    result = {0: (q, head, [], [])}
    for elapsed in range(1, LAST + 1):
        w, m, q = rows[q, right[0] if right else 0]
        assert q < 252, ('early halt', elapsed)
        right = [w] + right[1:]
        if m == 'R':
            left, right, head = [w] + left, right[1:], head + 1
        else:
            right, left, head = [left[0] if left else 0] + right, left[1:], head - 1
        if elapsed in targets:
            result[elapsed] = q, head, left[:], right[:]
    return depths, ends, result


def tree(rows):
    if len(rows) == 1:
        return f'.leaf ({action(rows[0][0], True)}, {action(rows[0][1], True)})'
    return f'.branch ({tree(rows[::2])}) ({tree(rows[1::2])})'


def boot_source(rows, mapping, depths, ends, points, left_margin, right_margin):
    state = mapping[96]
    source = f'''import BusyBeaver.ZFC.FiniteZipper
import BusyBeaver.ZFC.TablePerm252

/-!
Finite blank-tape prefix of the frozen register-permutation252 candidate.
Generated untrusted checkpoint data; all504 actions and25 finite zipper blocks
must be checked by Lean's kernel. Uses the generic FiniteZipper soundness proof.
At82552 moves: old96/canonical{state}, absolute head2, empty PC, gap40,
nine zero primary registers, all65 spare blocks (only spare8 is1),77 total ones.
No first-arrival, general runtime, compiler, logical or consistency theorem.
Old-label table SHA256: {OLD_SHA256}.
-/
namespace SetTheory.BusyBeaver.ZFC.BootPerm252
open FiniteZipper
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def zipInitialPerm252 : ZipConfig 252 :=
  {{ state := some ⟨0, by decide⟩, head := 0, left := [], right := [] }}

theorem zipInitialPerm252_rep : ZipRep (initial 252) zipInitialPerm252 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro i <;> rfl

def bootSparesPerm252 : List Nat := List.replicate 8 0 ++ [1] ++ List.replicate 56 0

def bootRegistersPerm252 : List Nat := List.replicate 9 0 ++ bootSparesPerm252

def registerBitsPerm252 (values : List Nat) : List Bool :=
  values.flatMap (fun v => false :: List.replicate (v + 1) true)

def bootTargetPerm252 : ZipConfig 252 :=
  {{ state := some ⟨{state}, by decide⟩, head := 2,
    left := true :: List.replicate {left_margin} false,
    right := List.replicate 40 false ++ [true] ++ registerBitsPerm252 bootRegistersPerm252 ++ List.replicate {right_margin} false }}

theorem bootSparesPerm252_length : bootSparesPerm252.length = 65 := by decide

theorem bootRegistersPerm252_length : bootRegistersPerm252.length = 74 := by decide

theorem bootRegistersPerm252_primary : bootRegistersPerm252.take 9 = List.replicate 9 0 := by decide

theorem bootSparesPerm252_values : ∀ i : Fin 65,
    bootSparesPerm252.getD i.val 0 = if i.val = 8 then 1 else 0 := by decide

inductive TransitionTree (states : Nat) where
  | leaf : (Action states × Action states) → TransitionTree states
  | branch : TransitionTree states → TransitionTree states → TransitionTree states

def TransitionTree.lookup {{n : Nat}} : TransitionTree n → Nat → (Action n × Action n)
  | .leaf row, _ => row
  | .branch even odd, q =>
    if q % 2 = 0 then even.lookup (q / 2) else odd.lookup (q / 2)

def fastTreePerm252 : TransitionTree 252 :=
{tree([(rows[q, 0], rows[q, 1]) for q in range(252)])}

def fastMachinePerm252 : Machine 252 where
  transition q b :=
    let row := fastTreePerm252.lookup q.val
    if b then row.2 else row.1

theorem fast_transition_eq : ∀ (q : Fin 252) (b : Bool),
    fastMachinePerm252.transition q b = machinePerm252.transition q b := by decide

theorem fastMachine_eq : fastMachinePerm252 = machinePerm252 := by
  have h : fastMachinePerm252.transition = machinePerm252.transition := by
    funext q b
    exact fast_transition_eq q b
  exact congrArg Machine.mk h

theorem advance_boot_checkpoint (elapsed depth : Nat) {{z z' : ZipConfig 252}}
    (before : ZipRep (machinePerm252.run elapsed) z)
    (calculated : zipBlock fastMachinePerm252 depth z = z') :
    ZipRep (machinePerm252.run (elapsed + 2 ^ depth)) z' := by
  rw [Machine.run_add_eq_runFrom]
  have h := zipBlock_sound fastMachinePerm252 depth before
  rw [calculated, fastMachine_eq] at h
  exact h

def bootCheckpoint0 : ZipConfig 252 := zipInitialPerm252

theorem coreCheckpoint0 : ZipRep (machinePerm252.run 0) bootCheckpoint0 :=
  zipInitialPerm252_rep

'''
    for count, (begin, end, depth) in enumerate(zip(ends, ends[1:], depths), 1):
        q, h, left, right = points[end]
        source += f'''def bootCheckpoint{end} : ZipConfig 252 :=
  {{ state := some ⟨{q}, by decide⟩, head := {h},
    left := {bits(left)}, right := {bits(right)} }}

theorem bootChunk{count} : zipBlock fastMachinePerm252 {depth} bootCheckpoint{begin} = bootCheckpoint{end} := by decide

theorem coreCheckpoint{end} : ZipRep (machinePerm252.run {end}) bootCheckpoint{end} :=
  advance_boot_checkpoint {begin} {depth} coreCheckpoint{begin} bootChunk{count}

'''
    source += f'''theorem final_boot_frame : bootCheckpoint{LAST} = bootTargetPerm252 := by decide

/-- The actual literal blank prefix, with the entire tape specified. -/
theorem fullBootstrapPerm252 : ZipRep (machinePerm252.run {LAST}) bootTargetPerm252 := by
  rw [← final_boot_frame]
  exact coreCheckpoint{LAST}

theorem fullBootstrapPerm252_state :
    (machinePerm252.run {LAST}).state = some ⟨{state}, by decide⟩ := fullBootstrapPerm252.1

theorem fullBootstrapPerm252_head :
    (machinePerm252.run {LAST}).head = 2 := fullBootstrapPerm252.2.1

theorem fullBootstrapPerm252_tape (pos : Int) :
    Tape.read (machinePerm252.run {LAST}).tape pos = frameRead bootTargetPerm252 pos :=
  read_eq_frameRead fullBootstrapPerm252 pos

theorem fullBootstrapPerm252_active_through :
    ∀ elapsed, elapsed ≤ {LAST} → (machinePerm252.run elapsed).state ≠ none := by
  apply active_through_of_endpoint
  rw [fullBootstrapPerm252_state]
  decide

theorem bootTargetPerm252_one_bits :
    (bootTargetPerm252.left ++ bootTargetPerm252.right).count true = 77 := by decide

#print axioms fast_transition_eq
#print axioms fastMachine_eq
#print axioms final_boot_frame
#print axioms fullBootstrapPerm252
#print axioms fullBootstrapPerm252_state
#print axioms fullBootstrapPerm252_head
#print axioms fullBootstrapPerm252_tape
#print axioms fullBootstrapPerm252_active_through
#print axioms bootTargetPerm252_one_bits
end SetTheory.BusyBeaver.ZFC.BootPerm252
'''
    return source


def generate(raw):
    old, states, mapping, rows = parse(raw)
    canonical = ('#! start 0\n' + ''.join(
        f'{q} {b} {w} {m} {t}\n' for (q, b), (w, m, t) in sorted(rows.items()))).encode()
    canonical_sha = hashlib.sha256(canonical).hexdigest()
    depths, ends, points = checkpoints(rows)
    q, head, left, right = points[LAST]
    assert q == mapping[96] and head == 2 and left[0] == 1 and not any(left[1:])
    values = [0] * 74
    values[17] = 1
    expected = [0] * 40 + [1] + [bit for v in values for bit in [0] + [1] * (v + 1)]
    assert right[:len(expected)] == expected and not any(right[len(expected):])
    ones = sorted([head-i-1 for i, b in enumerate(left) if b] + [head+i for i, b in enumerate(right) if b])
    assert len(ones) == 77 and len(left) >= 1 and len(right) >= len(expected)
    # Independent literal set-of-positions run on the original unrenumbered table.
    oq, oh, tape = 64, 0, set()
    for step in range(LAST):
        assert oq != 254
        w, m, oq = old[oq, int(oh in tape)]
        if w: tape.add(oh)
        else: tape.discard(oh)
        oh += 1 if m == 'R' else -1
    assert (oq, oh, sorted(tape)) == (96, 2, ones)
    metadata = {'scope':'Literal table renumbering and untrusted finite-prefix expected data; Lean compilation required separately.',
                'old_label_sha256':OLD_SHA256,'canonical_sha256':canonical_sha,
                'upstream':'297ab8df7e5de329605c3875b4934643b371a5e3',
                'public253':'0d544f2a2e3c18f12278441a74b7879f31cbe856',
                'physical_permutation':PERMUTATION,'working_states':252,'transition_rows':504,
                'old_start':64,'canonical_start':0,'old_halt':254,'canonical_halt':252,
                'canonical_to_old':states,'old_to_canonical':mapping,
                'blank_prefix':{'steps':LAST,'state_old':96,'state_canonical':q,'head':head,'gap':40,
                                'primary':[0]*9,'spares':[0]*8+[1]+[0]*56,'all_one_positions':ones,
                                'all_other_tape_cells_zero':True,'left_zip_length':len(left),'right_zip_length':len(right)},
                'checkpoint_depths':depths,'checkpoint_ends':ends,
                'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    return canonical, metadata, table_source(rows, canonical_sha), boot_source(rows, mapping, depths, ends, points, len(left)-1, len(right)-len(expected))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,default=DIRECTORY/'zfc_permutation252_old.tm')
    parser.add_argument('--candidate-dir',type=Path,default=DIRECTORY)
    parser.add_argument('--lean-dir',type=Path,default=LEAN_DIRECTORY)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    if not __debug__:parser.error('assertions must remain enabled')
    raw = args.source.read_bytes()
    canonical, metadata, table_lean, boot_lean = generate(raw)
    outputs = {args.candidate_dir/'zfc_permutation252_old.tm':raw,
               args.candidate_dir/'zfc_permutation252.tm':canonical,
               args.candidate_dir/'renumbering.json':(json.dumps(metadata,indent=2)+'\n').encode(),
               args.lean_dir/'TablePerm252.lean':table_lean.encode(),
               args.lean_dir/'BootPerm252.lean':boot_lean.encode()}
    for path, data in outputs.items():
        if args.check:
            if path.read_bytes() != data:parser.error(f'generated output differs: {path}')
        else:
            path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    print(json.dumps({'status':'CHECK PASS' if args.check else 'GENERATED (Lean not run)',
                      'canonical_sha256':metadata['canonical_sha256'],'state_canonical':metadata['blank_prefix']['state_canonical'],
                      'steps':LAST,'head':2,'whole_ones':77,'chunks':25,'outputs':[str(p) for p in outputs]},indent=2))


if __name__ == '__main__':
    main()
