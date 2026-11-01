import BusyBeaver.ZFC.Code254

/-!
The numerical calculus of the seed-K 222 and of the 221-state machine.

The 221 runs the register program of the seed-K 222 (same primitive word, same guarded
control flow), so its calculus is the 222's. Against Elliot Glazer's K230 calculus it differs
in two rows, with the base-4 codes and the remaining rows of `Code254`:

* rho7 is replaced by the merged equality row
  `G(a,b,c) = Eq(c,a) → (Eq(c,b) → ∀_{wel a b} Eq(a,b))` (Source 128);
* the gated bundle is the helper-free seed bundle `¬(RV → ¬K_s)` (Source 129 without the
  helper): membership vacuity `RV = Rel(a,b) → ∀c Rel(a,b)` and the seed core `K_s`, whose
  matrix and private label are both the code `c`.

The codes below are, number for number, those of the Rocq development
(`k225-formal/rocq224/src/Codes222.v`), which were checked against the pinned symbolic
executor of the emitted words.

Results here: `c222_sound` (every derivable code decodes to a formula true in every
irreflexive model of the decoded bundles), the classical propositional basis, and the
projections of the bundle.
-/

namespace SetTheory.BusyBeaver.ZFC.KCode222

open SetTheory.BusyBeaver.ZFC.Tarski
open SetTheory.BusyBeaver.ZFC.Code254
open NF

/-! ## Codes -/

/-- The merged equality row (replaces rho7). -/
def growG (a b c : Nat) : Nat := wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))

/-- The seed request `∀b (m → ¬∀b (m → ¬ b ∈ k))`. -/
def req (b k m : Nat) : Nat := wal b (wim m (wn (wal b (wim m (wn (wel b k))))))

/-- The seed closure `∀b (b ∈ k → ¬∀a (m → ¬∀a (a ⊆ b → req)))`, with `⊆` bound by `k`. -/
def clos (a b k m : Nat) : Nat :=
  wal b (wim (wel b k) (wn (wal a (wim m (wn (wal a (wim (wal k (wim (wel k a) (wel k b)))
    (req b k m))))))))

/-- The negated seed core, matrix and private label both `c`. -/
def nks (a b c : Nat) : Nat := wal c (wim (clos a b c c) (wn (req b c c)))

/-- Membership vacuity. -/
def vrel (a b c : Nat) : Nat := wim (wel a b) (wal c (wel a b))

/-- The helper-free seed bundle `¬(RV → ¬K_s)`. -/
def bundle222 (a b c : Nat) : Nat := wn (wim (vrel a b c) (nks a b c))

/-- The calculus at the level of codes. -/
inductive C222 : Nat → Prop
  | truth : C222 0
  | mp {t b : Nat} : C222 t → C222 (wim t b) → C222 b
  | gen (a : Nat) {h : Nat} : C222 h → C222 (wal a h)
  | r1 (a b : Nat) : C222 (rho1 a b)
  | r2 (a b c : Nat) : C222 (rho2 a b c)
  | r3 (a b c : Nat) : C222 (rho3 a b c)
  | r4 (a b c : Nat) : C222 (rho4 a b c)
  | r5 (a b c : Nat) : C222 (rho5 a b c)
  | r6 (a b : Nat) : C222 (rho6 a b)
  | rG (a b c : Nat) : C222 (growG a b c)
  | r8 (a b c u : Nat) : C222 (rho8 a b c u)
  | bundle (a b c : Nat) : c ≠ a → c ≠ b → C222 (bundle222 a b c)

theorem lt_wel_left (a b : Nat) : a < wel a b := by
  have := le_P_left a b; simp only [wel]; omega

theorem lt_wel_right (a b : Nat) : b < wel a b := by
  have := le_P_right a b; simp only [wel]; omega

/-! ## Soundness -/

universe u
variable {V : Type u}

/-- The merged equality row is valid in every structure. -/
theorem growG_valid (mem : V → V → Prop) (e : Nat → V) (a b c : Nat) :
    Tarski.Sat mem e (dec (growG a b c)) := by
  simp only [growG]
  rw [sat_wim, sat_weq, sat_wim, sat_weq, sat_wal]
  intro h1 h2 d
  rw [sat_weq, update_other _ _ (Nat.ne_of_lt (lt_wel_left a b)),
    update_other _ _ (Nat.ne_of_lt (lt_wel_right a b)), ← h1, ← h2]

/-- Every derivable code decodes to a formula true in every irreflexive model of the
decoded bundles. -/
theorem c222_sound {D : Type u} (mem : D → D → Prop) (hirr : ∀ x, ¬ mem x x)
    (hB : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → D, Tarski.Sat mem e (dec (bundle222 a b c))) :
    ∀ {n : Nat}, C222 n → ∀ e : Nat → D, Tarski.Sat mem e (dec n) := by
  intro n hn
  induction hn with
  | truth => exact fun e => sat_T0 mem e
  | mp _ _ ih1 ih2 => exact fun e => (sat_wim mem e _ _).mp (ih2 e) (ih1 e)
  | gen a _ ih => exact fun e => (sat_wal mem e a _).mpr fun d => ih _
  | r1 a b => exact fun e => (rows_valid mem hirr e).1 a b
  | r2 a b c => exact fun e => (rows_valid mem hirr e).2.1 a b c
  | r3 a b c => exact fun e => (rows_valid mem hirr e).2.2.1 a b c
  | r4 a b c => exact fun e => (rows_valid mem hirr e).2.2.2.1 a b c
  | r5 a b c => exact fun e => (rows_valid mem hirr e).2.2.2.2.1 a b c
  | r6 a b => exact fun e => (rows_valid mem hirr e).2.2.2.2.2.1 a b
  | rG a b c => exact fun e => growG_valid mem e a b c
  | r8 a b c u => exact fun e => (rows_valid mem hirr e).2.2.2.2.2.2.2 a b c u
  | bundle a b c h1 h2 => exact hB a b c h1 h2

/-- If the code 1 is derivable, the decoded bundles have no irreflexive model. -/
theorem no_model_of_c222_one (h : C222 F) {D : Type u} (mem : D → D → Prop)
    (hirr : ∀ x, ¬ mem x x)
    (hB : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → D, Tarski.Sat mem e (dec (bundle222 a b c)))
    (e : Nat → D) : False :=
  sat_F mem hirr e (c222_sound mem hirr hB h e)

/-! ## The propositional basis -/

theorem implicational : Lukasiewicz.Implicational wim C222 where
  mp := fun h1 h2 => C222.mp h2 h1
  rho8 := fun c u a b => C222.r8 a b c u

theorem c222_k (a b : Nat) : C222 (wim a (wim b a)) := Lukasiewicz.k implicational a b
theorem c222_s (a b c : Nat) : C222 (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  Lukasiewicz.s implicational a b c

theorem c222_efq (a : Nat) : C222 (wim F a) := by
  have h1 : C222 (wim F (wex 0 (wal 0 a))) := c222_k F (wal 0 (wn (wal 0 a)))
  have h2 : C222 (wim F (wim (wex 0 (wal 0 a)) a)) := C222.mp (C222.r6 0 a) (c222_k _ F)
  exact C222.mp h1 (C222.mp h2 (c222_s F (wex 0 (wal 0 a)) a))

theorem c222_classical : Kalmar.Classical wim F C222 where
  mp := fun h1 h2 => C222.mp h2 h1
  k := c222_k
  s := c222_s
  peirce := Lukasiewicz.peirce implicational
  efq := c222_efq

#print axioms c222_sound
#print axioms c222_classical

end SetTheory.BusyBeaver.ZFC.KCode222
