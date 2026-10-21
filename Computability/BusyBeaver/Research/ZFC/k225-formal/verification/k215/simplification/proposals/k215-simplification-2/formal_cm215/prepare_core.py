#!/usr/bin/env python3
"""Prepare a pinned six-module repository subset and the exact dense instance."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess
from check_marker_certificate import parse

HERE = Path(__file__).resolve().parent
p = argparse.ArgumentParser()
p.add_argument('--repo', type=Path, required=True)
a = p.parse_args()
base = a.repo / 'Computability/BusyBeaver'
modules = ['BusyBeaver/Core', 'BusyBeaver/ZFC/KZip', 'BusyBeaver/ZFC/KTableCore',
           'BusyBeaver/ZFC/KTable215', 'BusyBeaver/ZFC/KDenseBridge', 'BusyBeaver/ZFC/KDense215']
pins = []
for name in modules:
    src = base / 'Lean' / (name + '.lean')
    dest = HERE / 'vendor' / (name + '.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dest)
    pins.append({'path': str(src.relative_to(a.repo)), 'local': str(dest.relative_to(HERE)),
                 'sha256': hashlib.sha256(dest.read_bytes()).hexdigest()})
shutil.copyfile(a.repo / 'LICENSE', HERE / 'vendor' / 'LICENSE.ProveIt')
source = base / 'Research/ZFC/candidate-k215'
oldmap = {int(k): int(v) for k,v in json.loads((source/'canonicalization.json').read_text())['native_to_canonical'].items()}
newmap = {int(k): int(v) for k,v in json.loads((source/'alternatives/conditional-marker/machine/canonicalization.json').read_text())['native_to_dense'].items()}
assert oldmap == newmap and oldmap[254] == 215 and oldmap[0] == 0
reverse = {v:k for k,v in oldmap.items()}
shutil.copyfile(source/'k215.tm', HERE/'k215.tm')
shutil.copyfile(source/'alternatives/conditional-marker/machine/marker215.tm', HERE/'cm215.tm')
_, rows, _ = parse(HERE/'cm215.tm')
assert {q for q,b in rows} == set(range(215))

parts = ['''import CM215Exact
import CoreNativeBridge
import BusyBeaver.ZFC.KDense215

namespace CM215Core
open SetTheory.BusyBeaver MarkerTransfer CoreNativeBridge
open SetTheory.BusyBeaver.ZFC
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- The literal CM215 dense table, states 0 through 214 and separate halt 215. -/
def rowsCM : List ((Bool × Bool × Nat) × (Bool × Bool × Nat)) := [''']
for q in range(215):
    def action(x):
        w,d,z = x
        return f'({str(bool(w)).lower()}, {str(d == 1).lower()}, {z})'
    parts.append('  (' + action(rows[q,0]) + ', ' + action(rows[q,1]) + ')' + (',' if q<214 else ']'))
parts.append('''
/-- The alternative as the repository's original Machine 215 type. -/
def machineCM215 : Machine 215 where
  transition q b :=
    let r := rowsCM.getD q.val ((false, true, 215), (false, true, 215))
    KDense215.act (if b then r.2 else r.1)
''')
parts.append('def nativeLabels : List Q := [' + ', '.join(str(reverse[q]) for q in range(215)) + ']\n')
parts.append('''def ex (q : Fin 215) : Q := nativeLabels.getD q.val 254

theorem old_compatible : Compatible KDense215.machine215 CM215Exact.old ex 254 := by
  unfold Compatible
  decide
theorem new_compatible : Compatible machineCM215 CM215Exact.new ex 254 := by
  unfold Compatible
  decide
theorem ex_start : ex 0 = 0 := rfl

theorem old_blank_iff : KDenseBridge.BlankHalts KDense215.machine215 ↔
    ∃ k, Halt CM215Exact.old
      (PositiveSimulation.iter (next CM215Exact.old) k ⟨0, 0, fun _ => false⟩) :=
  CoreNativeBridge.blank_iff old_compatible CM215Exact.old_halt ex_start

theorem new_blank_iff : KDenseBridge.BlankHalts machineCM215 ↔
    ∃ k, Halt CM215Exact.new
      (PositiveSimulation.iter (next CM215Exact.new) k ⟨0, 0, fun _ => false⟩) :=
  CoreNativeBridge.blank_iff new_compatible CM215Exact.new_halt ex_start

/-- Compiled exact-table transfer in the unchanged repository's own semantics. -/
theorem blank_halts_iff_primary :
    KDenseBridge.BlankHalts machineCM215 ↔ KDenseBridge.BlankHalts KDense215.machine215 :=
  new_blank_iff.trans (CM215Exact.blank_equihalt.symm.trans old_blank_iff.symm)

#print axioms old_compatible
#print axioms new_compatible
#print axioms blank_halts_iff_primary
end CM215Core
''')
(HERE/'CM215Core.lean').write_text('\n'.join(parts))
try:
    head = subprocess.check_output(['git','-C',str(a.repo),'rev-parse','HEAD'], text=True).strip()
except subprocess.CalledProcessError:
    head = None
(HERE/'upstream-pins.json').write_text(json.dumps({'repository':'https://github.com/VladimirReshetnikov/ProveIt', 'commit': head, 'files':pins},indent=2)+'\n')
