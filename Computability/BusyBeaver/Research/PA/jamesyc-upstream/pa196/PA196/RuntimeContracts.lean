module
public import PA196.Table
public import M6.Runtime

/-!
Candidate-specific reuse of the existing all-natural symbolic runtime theorem.
These files are generated proof sources, not a claim that Lean has checked them.
The candidate table is supplied separately in PA196.Table using raw
sparse labels (ROOT84, halt254), with its own generic native_boxes instance.
-/

@[expose] public section

namespace PA196.RuntimeContracts
open M6.Zip M6.Runtime PA196.Table

structure Contract where
  branch : Branch
  initial : SConf
  target : SConf
  deriving Repr

def check (fuel : Nat) (c : Contract) : Bool :=
  (exec machine c.branch (fun s => sMatches s c.target) fuel c.initial false).isSome

/-- Exact complete symbolic endpoints, arbitrary natural gap and valid full file,
with at least one concrete machine transition. -/
theorem sound (fuel : Nat) (c : Contract) (hc : check fuel c = true)
    (n : Nat) (vs : List Nat) (hv : Valid c.branch vs) :
    Reach1 machine (conc n vs c.initial) (conc n vs c.target) := by
  unfold check at hc
  cases he : exec machine c.branch (fun s => sMatches s c.target) fuel c.initial false with
  | none => simp [he] at hc
  | some last =>
      have h := exec_sound native_boxes n hv fuel c.initial false last he
      have hm := sMatches_conc n vs h.1
      simpa only [hm] using h.2.2 rfl

def rootFrame (path : List Bool) (extra : Nat := 0) (effect : Eff := .none) : SConf :=
  (84, false, [.bit true],
    path.map Seg.bit ++ [.run false 1 (48 + extra - path.length),
      .bit true, .box (.plain effect)])

def haltCheck (fuel : Nat) (br : Branch) (initial : SConf) : Bool :=
  (exec machine br (fun s => s.1 == 254) fuel initial false).isSome

private theorem conc_control (n : Nat) (vs : List Nat) (s : SConf) :
    (conc n vs s).q = s.1 := by
  rcases s with ⟨q,onLeft,l,r⟩
  cases onLeft <;> rfl

theorem halt_positive_sound (fuel : Nat) (br : Branch) (initial : SConf)
    (hc : haltCheck fuel br initial = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) :
    ∃ final, Reach1 machine (conc n vs initial) final ∧ final.q = 254 := by
  unfold haltCheck at hc
  cases he : exec machine br (fun s => s.1 == 254) fuel initial false with
  | none => simp [he] at hc
  | some last =>
      have h := exec_sound native_boxes n hv fuel initial false last he
      refine ⟨conc n vs last,h.2.2 rfl,?_⟩
      rw [conc_control]
      exact beq_iff_eq.mp h.1

theorem halt_sound (fuel : Nat) (br : Branch) (initial : SConf)
    (hc : haltCheck fuel br initial = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) :
    Halts machine (conc n vs initial) := by
  obtain ⟨final,hreach,hq⟩ := halt_positive_sound fuel br initial hc n vs hv
  refine ⟨final,hreach.reach,?_⟩
  simp [M6.Zip.step,hq,PA196.Table.terminal_row]

structure CertifiedContract where
  site : Nat
  successor : Nat
  extra : Nat
  effect : Eff
  contract : Contract
  fuel : Nat
  checked : check fuel contract = true

theorem certified_sound (c : CertifiedContract) (n : Nat) (vs : List Nat)
    (hv : Valid c.contract.branch vs) :
    Reach1 machine (conc n vs c.contract.initial) (conc n vs c.contract.target) :=
  sound c.fuel c.contract c.checked n vs hv

structure CertifiedHalt where
  site : Nat
  branch : Branch
  initial : SConf
  fuel : Nat
  checked : haltCheck fuel branch initial = true

theorem certified_halt_sound (c : CertifiedHalt) (n : Nat) (vs : List Nat)
    (hv : Valid c.branch vs) : Halts machine (conc n vs c.initial) :=
  halt_sound c.fuel c.branch c.initial c.checked n vs hv

end PA196.RuntimeContracts
