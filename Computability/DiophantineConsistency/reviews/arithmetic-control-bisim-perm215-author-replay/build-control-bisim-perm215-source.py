from pathlib import Path
import hashlib, json, re

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
B = R / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'

def record(p):
    p = Path(p)
    return dict(path=str(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest())

def rows(name, key, expected):
    p = B / (name + '.lean')
    assert record(p)['sha256'] == expected
    literal = re.search(r'def ' + key + r' : Nat := 0x([0-9a-f]+)', p.read_text())[1]
    packed = int(literal, 16)
    assert packed < 1 << (36 * 4751)
    result = []
    for i in range(4751):
        x = (packed >> (36 * i)) % (1 << 36)
        assert x < 1 << 33
        reg = (x >> 3) % 16
        assert reg < 9
        result.append([x % 8, reg, (x >> 7) % 8192, (x >> 20) % 8192])
    return result, record(p)

A, ap = rows('ArithmeticDagControlPerm222', 'packedRows', '1851444d564e63c2296c2e64335d95008465da9c1fd837bef399886f691e7fb4')
C, cp = rows('ArithmeticControl215Table', 'packed215', '124d6a19e02d8ac41cfc2fe859b142d015995db623f6ef073bd37ef72396d8a5')
cuts = sorted({1} | {s for row in A if row[0] == 2 for s in row[2:]})
assert len(cuts) == 2850 and cuts[0] == 1
index = {c:i for i,c in enumerate(cuts)}

def segment(table, control, fuel):
    offset = [0] * 9
    for clock in range(1, fuel + 1):
        assert 1 <= control <= len(table)
        row = table[control - 1]
        if row[0] in [2, 4]:
            return control, offset, clock
        assert row[0] in [1, 3]
        if row[0] == 1:
            offset[row[1]] += 1
        control = row[2]
    raise AssertionError('fuel insufficient')

entries = []
maxfuel = 0
for pc in cuts:
    ca, oa, fa = segment(A, pc, 6)
    cb, ob, fb = segment(C, pc, 6)
    assert ca == cb and oa == ob
    ra, rb = A[ca-1], C[cb-1]
    assert ra == rb
    if ra[0] == 4:
        s0 = s1 = 0
    else:
        assert ra[0] == 2
        s0, s1 = index[ra[2]], index[ra[3]]
    entries.append([pc, pc, [0]*9, [0]*9, s0, s1])
    maxfuel = max(maxfuel, fa, fb)
entryhash = hashlib.sha256(json.dumps(entries, separators=(',', ':')).encode()).hexdigest()
assert entryhash == '22677a305a6889a1d731f1d78467314bca4ae1f9a889705fffed70d61065b6db'
assert maxfuel == 6
packed = 0
for i,(a,b,alpha,beta,s0,s1) in enumerate(entries):
    assert 0 < a == b < 8192 and s0 < 2850 and s1 < 2850
    assert alpha == beta == [0]*9
    slot = a + (b << 13) + (s0 << 62) + (s1 << 74)
    assert slot < 1 << 86
    packed |= slot << (96*i)
assert packed < 1 << (96*2850)
roundtrip = []
for i in range(2850):
    x = (packed >> (96*i)) % (1 << 96)
    assert x < 1 << 86
    alpha = [(x >> (26+2*j)) % 4 for j in range(9)]
    beta = [(x >> (44+2*j)) % 4 for j in range(9)]
    roundtrip.append([x % 8192, (x >> 13) % 8192, alpha, beta, (x >> 62) % 4096, (x >> 74) % 4096])
assert roundtrip == entries

head = '''import BusyBeaver.ZFC.ArithmeticControl215Table

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! Complete internal offset-segment bisimulation of actual DagPerm and p215.
Every certificate entry is kernel checked against both accepted packed tables.
This compares the two represented control interpreters, not the Turing machine
or the source-ZFC/HA endpoints. -/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlBisimPerm215

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlBisim ArithmeticControlTable
open ArithmeticControlFile (regValue fileValue liveValue reg_file live_ne_zero
  liveDef projectionDef projection_defined)

def certSize : Nat := 2850
def fuel : Nat := 6
def zeros : Vec := [0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All 2,850 complete 96-bit entries; the two nine-element offset fields are zero. -/
def packedCert : Nat := 0x'''+format(packed,'x')+'''

def cert (i : Nat) : Option Entry := PackedTables.certOf packedCert certSize i

theorem packedCert_bound : packedCert < 2 ^ (96 * certSize) := by decide +kernel

private abbrev EntryShape (i : Nat) : Prop :=
  PackedTables.slot packedCert i 96 < 2 ^ 86 ∧
    match cert i with
    | none => False
    | some e => e.a = e.b ∧ e.α = zeros ∧ e.β = zeros

private abbrev block (k : Nat) : Prop :=
  ∀ j : Fin 64, 64 * k + j.val < certSize →
    entryOK ArithmeticDagControlPerm222.rowsLit ArithmeticControl215Table.rows215
      cert fuel certSize (64 * k + j.val) = true ∧ EntryShape (64 * k + j.val)

'''
blocks = ''.join(f'private theorem block_{i} : block {i} := by decide +kernel\n' for i in range(45))
wiring = '(fun i => Fin.elim0 i)'
for i in reversed(range(45)):
    wiring = f'(Fin.cases block_{i} {wiring})'
root = entries[0]
tail = '''
private theorem blocks_checked : ∀ k : Fin 45, block k.val :=
  '''+wiring+'''

/-- Every actual index is covered, including the final block's 34 entries. -/
private theorem all_entries (i : Nat) (hi : i < certSize) :
    entryOK ArithmeticDagControlPerm222.rowsLit ArithmeticControl215Table.rows215
      cert fuel certSize i = true ∧ EntryShape i := by
  have hk : i / 64 < 45 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by
    change i < 2850 at hi
    omega)
  have h := blocks_checked ⟨i / 64, hk⟩ ⟨i % 64, Nat.mod_lt _ (by decide)⟩
  simp only [Nat.div_add_mod] at h
  exact h hi

theorem check_all (i : Nat) (hi : i < certSize) :
    entryOK ArithmeticDagControlPerm222.rowsLit ArithmeticControl215Table.rows215
      cert fuel certSize i = true := (all_entries i hi).1

/-- No reserved high bits occur in any complete certificate slot. -/
theorem reserved_bits (i : Nat) (hi : i < certSize) :
    PackedTables.slot packedCert i 96 < 2 ^ 86 := (all_entries i hi).2.1

/-- Every entry, not just the root, has equal controls and both literal zero vectors. -/
theorem entry_diagonal_offsets (i : Nat) (hi : i < certSize) :
    ∃ e, cert i = some e ∧ e.a = e.b ∧ e.α = zeros ∧ e.β = zeros := by
  obtain ⟨e, he, _, _, _, _⟩ :=
    entryOK_spec ArithmeticDagControlPerm222.rowsLit ArithmeticControl215Table.rows215
      cert fuel certSize i (check_all i hi)
  exact ⟨e, he, by simpa only [he] using (all_entries i hi).2.2⟩

theorem cert_outside (i : Nat) (hi : certSize ≤ i) : cert i = none := by
  simp only [cert, PackedTables.certOf, if_neg (Nat.not_lt.mpr hi)]

def rootEntry : Entry := ⟨1, 1, zeros, zeros, '''+str(root[4])+', '+str(root[5])+'''⟩

theorem cert_zero : cert 0 = some rootEntry := by decide +kernel
theorem root_controls : rootEntry.a = 1 ∧ rootEntry.b = 1 := ⟨rfl, rfl⟩
theorem root_offsets :
    (∀ p : Fin 9, vget rootEntry.α p = 0) ∧
    (∀ p : Fin 9, vget rootEntry.β p = 0) := by decide +kernel

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance proj_defined (p : Fin 9) :
    𝚺₁-Function₁[V] (fun x => regValue x p) via projectionDef 8 p :=
  projection_defined 8 p

/-- Both directions use internal times and an arbitrary internal nine-register file. -/
theorem halts_iff (x : V) :
    (∃ t : V, ArithmeticDagControlPerm222.run t (liveValue 1 x) = 0) ↔
      (∃ t : V, ArithmeticControl215Table.run215 t (liveValue 1 x) = 0) := by
  have h := halts_iff_of_check (reg := regValue) (write := write) (live := liveValue)
    fileValue reg_file live_ne_zero liveDef (fun p => projectionDef 8 p)
    (stepValue ArithmeticDagControlPerm222.table) (stepValue ArithmeticControl215Table.table215)
    ArithmeticDagControlPerm222.run ArithmeticControl215Table.run215
    ArithmeticDagControlPerm222.rowsLit ArithmeticControl215Table.rows215 cert fuel certSize
    ArithmeticDagControlPerm222.run_zero ArithmeticControl215Table.run215_zero
    ArithmeticDagControlPerm222.run_add ArithmeticControl215Table.run215_add
    ArithmeticDagControlPerm222.run_one ArithmeticControl215Table.run215_one
    ArithmeticDagControlPerm222.run_halted ArithmeticControl215Table.run215_halted
    ArithmeticDagControlPerm222.spec ArithmeticControl215Table.spec215
    reg_write_same reg_write_other check_all rootEntry cert_zero (by decide)
    root_offsets.1 root_offsets.2 x
  simpa only [rootEntry, Nat.cast_one] using h

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlBisimPerm215
'''
main = B/'ArithmeticControlBisimPerm215.lean'
checks = B/'ArithmeticControlBisimPerm215Checks.lean'
assert not main.exists() and not checks.exists()
main.write_text(head+blocks+tail)
checks.write_text('''import BusyBeaver.ZFC.ArithmeticControlBisimPerm215

set_option autoImplicit false
set_option Elab.async false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlBisimPerm215Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlBisimPerm215
open ArithmeticControlBisim (Vec entryOK)
open ArithmeticControlFile (liveValue)

example : certSize = 2850 := rfl
example : fuel = 6 := rfl
example : zeros.length = 9 := rfl
example : zeros ≠ ([] : Vec) := by decide
example : rootEntry.s0 = 2 ∧ rootEntry.s1 = 1 := ⟨rfl, rfl⟩
example : cert 0 = some rootEntry := cert_zero
example : entryOK ArithmeticDagControlPerm222.rowsLit ArithmeticControl215Table.rows215
    cert fuel certSize 2849 = true := check_all 2849 (by decide)
example : PackedTables.slot packedCert 2849 96 < 2 ^ 86 := reserved_bits 2849 (by decide)
example : cert 2850 = none := cert_outside 2850 (by decide)

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem forward (x : V)
    (h : ∃ t : V, ArithmeticDagControlPerm222.run t (liveValue 1 x) = 0) :
    ∃ t : V, ArithmeticControl215Table.run215 t (liveValue 1 x) = 0 := (halts_iff x).mp h

theorem backward (x : V)
    (h : ∃ t : V, ArithmeticControl215Table.run215 t (liveValue 1 x) = 0) :
    ∃ t : V, ArithmeticDagControlPerm222.run t (liveValue 1 x) = 0 := (halts_iff x).mpr h
end Model

#print axioms packedCert_bound
#print axioms check_all
#print axioms reserved_bits
#print axioms entry_diagonal_offsets
#print axioms cert_outside
#print axioms cert_zero
#print axioms root_controls
#print axioms root_offsets
#print axioms halts_iff
#print axioms forward
#print axioms backward
end SetTheory.BusyBeaver.ZFC.ArithmeticControlBisimPerm215Checks
''')
audit = dict(scope='Full fixed-table candidate reconstruction and round-trip, subordinate to actual kernel entryOK checks.',
    tables=[ap, cp], row_counts=[len(A), len(C)], entries=2850, entries_sha256=entryhash,
    fuel=6, max_fuel=maxfuel, root_entry=root, all_offsets_explicit_nine_zeros=True,
    all_reserved_bits_zero=True, complete_packed_high_bits_zero=True,
    packed_bits=packed.bit_length(), packed_hex_digits=len(format(packed,'x')),
    packed_hex_sha256=hashlib.sha256(format(packed,'x').encode()).hexdigest(),
    generator=record(__file__), main=record(main), checks=record(checks))
Path('/tmp/control-bisim-perm215-source-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps(audit,indent=2))
