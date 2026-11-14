import PA195RuntimeEngine

/-! PA195-specific adaptation of the upstream PA196 runtime-contract
interface. The machine is the exact unfolded PA195 parent. -/

@[expose] public section

namespace PA195RuntimeContracts
open M6.Zip M6.Runtime PA195RuntimeEngine

theorem terminal_row (b : Bool) : machine 254 b = none := by
  cases b <;> decide +kernel

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
      have h := exec_sound box_lemmas n hv fuel c.initial false last he
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
      have h := exec_sound box_lemmas n hv fuel initial false last he
      refine ⟨conc n vs last,h.2.2 rfl,?_⟩
      rw [conc_control]
      exact beq_iff_eq.mp h.1

theorem halt_sound (fuel : Nat) (br : Branch) (initial : SConf)
    (hc : haltCheck fuel br initial = true)
    (n : Nat) (vs : List Nat) (hv : Valid br vs) :
    Halts machine (conc n vs initial) := by
  obtain ⟨final,hreach,hq⟩ := halt_positive_sound fuel br initial hc n vs hv
  refine ⟨final,hreach.reach,?_⟩
  simp [M6.Zip.step,hq,terminal_row]


end PA195RuntimeContracts
