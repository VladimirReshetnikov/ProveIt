import BusyBeaver.ZFC.Lukasiewicz

/-!
The original four-tag numerical calculus, with its actual bundled axiom.

Definitions port `Codes254.v`, `Thm254.v`, and `Enum254.gate` from Jeff's
verification of Mira-Cult's machine, busy-beaver commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. The public253 pin
`0d544f2a2e3c18f12278441a74b7879f31cbe856` reuses these same definitions.
This attributed port does not relicense the upstream snapshot.

Code0 is a separate truth axiom with `wim 0 0 = 0`; code1 is the atom
`wel 0 0`, used as relative falsity. No semantic interpretation of code1
is assumed here. Both gated vacuity families are derived from the whole
original C/G/vacuity bundle, rather than added as numerical axioms.
This module proves no decoder, theory calibration, enumerator simulation,
binary-table endpoint or new state bound.
-/

namespace SetTheory.BusyBeaver.ZFC.Numeric254

def tri : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + tri n

def P (a b : Nat) : Nat := tri (a + b) + b

def wim (a b : Nat) : Nat := 4 * P a b
def wel (i j : Nat) : Nat := 4 * P i j + 1
def wal (i a : Nat) : Nat := 4 * P i a + 2
def weq (i j : Nat) : Nat := 4 * P i j + 3
def F : Nat := 1
def wn (a : Nat) : Nat := wim a F
def wa (a b : Nat) : Nat := wn (wim a (wn b))
def wex (i a : Nat) : Nat := wn (wal i (wn a))

-- Keep the original numeric parameter order a,b,c,u.
def rho8 (a b c u : Nat) : Nat :=
  wim (wim (wim c u) a) (wim (wim a c) (wim b c))
def rho7 (a b c : Nat) : Nat := wim (weq c a) (wim (weq c b) (weq a b))
def rho6 (a b : Nat) : Nat := wim (wex a (wal a b)) b
def rho5 (a b c : Nat) : Nat := wim (weq c a) (wim (wel c b) (wel a b))
def rho4 (a b c : Nat) : Nat := wim (wal a (wal b c)) (wal b (wal a c))
def rho3 (a b c : Nat) : Nat := wim (weq a b) (wim (wel c a) (wel c b))
def rho2 (a b c : Nat) : Nat :=
  wim (wal a (wim b c)) (wim (wal a b) (wal a c))
def rho1 (a b : Nat) : Nat := wex a (weq a b)

def bundleC (a b c : Nat) : Nat :=
  wex b (wa (wal a (wim (wel a b)
    (wa (wex c (wa (wal b (wim (wal c (wim (wel c b) (wel c a))) (wel b c)))
      (wel c b)))
      (wal c (wim (wel c a) (wel c b))))))
    (wel c b))

def bundleG (a b c : Nat) : Nat :=
  wex c (wa (wal a (wim (wel a b) (wal b (wim c (wex b (wa c (wel b c)))))))
    (wal b (wim (wel b c) (wex a c))))

def bundle (a b c : Nat) : Nat :=
  wa (wa (bundleC a b c) (bundleG a b c))
    (wa (wim (wel a b) (wal c (wel a b))) (wim (weq a b) (wal c (weq a b))))

/-- The actual failed-gate result is the truth code0. -/
def gate (a b c : Nat) : Nat :=
  if c == a || c == b then 0 else bundle a b c

/-- Exactly the twelve constructors of the published numerical calculus.
MP retains the source's minor-premise then major-premise order. -/
inductive NumThm : Nat → Prop
  | truth : NumThm 0
  | mp {t b : Nat} : NumThm t → NumThm (wim t b) → NumThm b
  | gen (i : Nat) {h : Nat} : NumThm h → NumThm (wal i h)
  | rho1 (a b : Nat) : NumThm (rho1 a b)
  | rho2 (a b c : Nat) : NumThm (rho2 a b c)
  | rho3 (a b c : Nat) : NumThm (rho3 a b c)
  | rho4 (a b c : Nat) : NumThm (rho4 a b c)
  | rho5 (a b c : Nat) : NumThm (rho5 a b c)
  | rho6 (a b : Nat) : NumThm (rho6 a b)
  | rho7 (a b c : Nat) : NumThm (rho7 a b c)
  | rho8 (a b c u : Nat) : NumThm (rho8 a b c u)
  | bundle (a b c : Nat) : c ≠ a → c ≠ b → NumThm (bundle a b c)

theorem truth_alias : wim 0 0 = 0 := rfl
theorem relative_falsity_atom : wel 0 0 = F := rfl

/-- Major-premise first interface for the generic propositional proofs. -/
theorem detach {a b : Nat} (hab : NumThm (wim a b)) (ha : NumThm a) : NumThm b :=
  .mp ha hab

private theorem implicational : Lukasiewicz.Implicational wim NumThm where
  mp := detach
  rho8 := fun c u a b => NumThm.rho8 a b c u

theorem k (a b : Nat) : NumThm (wim a (wim b a)) :=
  Lukasiewicz.k implicational a b

theorem s (a b c : Nat) :
    NumThm (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  Lukasiewicz.s implicational a b c

theorem peirce (a b : Nat) : NumThm (wim (wim (wim a b) a) a) :=
  Lukasiewicz.peirce implicational a b

/-- Numeric explosion uses the original rho6, including when its binder is0. -/
theorem ex_falso (a : Nat) : NumThm (wim F a) := by
  let x := wal 0 (wn (wal 0 a))
  let e := wex 0 (wal 0 a)
  have hfe : NumThm (wim F e) := k F x
  have hfea : NumThm (wim F (wim e a)) :=
    detach (k (wim e a) F) (.rho6 0 a)
  exact detach (detach (s F e a) hfea) hfe

/-- An actually constructed basis for every numeric parameter, including0. -/
theorem classical : Kalmar.Classical wim F NumThm where
  mp := detach
  k := k
  s := s
  peirce := peirce
  efq := ex_falso

theorem self_imp (a : Nat) : NumThm (wim a a) := Kalmar.self_imp classical a

private theorem thm_of_der0 {a : Nat} (d : Kalmar.Der wim NumThm [] a) : NumThm a :=
  d.sound classical (fun _ h => absurd h List.not_mem_nil)

private theorem dne (a : Nat) : NumThm (wim (wn (wn a)) a) := by
  have inner : Kalmar.Der wim NumThm [wn (wn a)] (wim (wn a) a) :=
    Kalmar.deduction classical
      (.mp (.ax (ex_falso a))
        (.mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) .cons_head))
  exact thm_of_der0 (Kalmar.deduction classical (.mp (.ax (peirce a F)) inner))

/-- Left projection for the actual relative-falsity conjunction. -/
theorem and_left {a b : Nat} (h : NumThm (wa a b)) : NumThm a := by
  have nb : Kalmar.Der wim NumThm [a, wn a] (wn b) :=
    .mp (.ax (ex_falso (wn b)))
      (.mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))) .cons_head)
  have hf : Kalmar.Der wim NumThm [wn a] F :=
    .mp (.ax h) (Kalmar.deduction classical nb)
  exact detach (dne a) (thm_of_der0 (Kalmar.deduction classical hf))

/-- Right projection for the actual relative-falsity conjunction. -/
theorem and_right {a b : Nat} (h : NumThm (wa a b)) : NumThm b := by
  have nb : Kalmar.Der wim NumThm [a, wn b] (wn b) :=
    .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hf : Kalmar.Der wim NumThm [wn b] F :=
    .mp (.ax h) (Kalmar.deduction classical nb)
  exact detach (dne b) (thm_of_der0 (Kalmar.deduction classical hf))

/-- This family is projected from the original bundle, with its exact gates. -/
theorem vacuity_rel (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) :
    NumThm (wim (wel a b) (wal c (wel a b))) := by
  have hv : NumThm (wa (wim (wel a b) (wal c (wel a b)))
      (wim (weq a b) (wal c (weq a b)))) :=
    and_right (.bundle a b c hca hcb)
  exact and_left hv

/-- Equality vacuity is likewise a consequence, rather than a new axiom. -/
theorem vacuity_eq (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) :
    NumThm (wim (weq a b) (wal c (weq a b))) := by
  have hv : NumThm (wa (wim (wel a b) (wal c (wel a b)))
      (wim (weq a b) (wal c (weq a b)))) :=
    and_right (.bundle a b c hca hcb)
  exact and_right hv

/-- Both failed and successful runtime gates produce numerical theorems. -/
theorem gate_thm (a b c : Nat) : NumThm (gate a b c) := by
  cases Nat.decEq c a with
  | isTrue hca => simpa [gate, hca] using NumThm.truth
  | isFalse hca =>
    cases Nat.decEq c b with
    | isTrue hcb => simpa [gate, hcb] using NumThm.truth
    | isFalse hcb => simpa [gate, hca, hcb] using NumThm.bundle a b c hca hcb

end SetTheory.BusyBeaver.ZFC.Numeric254
