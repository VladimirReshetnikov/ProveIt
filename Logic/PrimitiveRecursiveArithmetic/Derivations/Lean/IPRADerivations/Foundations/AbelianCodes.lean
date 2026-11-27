import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Header

/-!
# Abelian groups on natural-number codes

The abstract group layer of `diophantine_geometry_ipra`, Theorem `thm:generation`: "Fix an abelian group
represented by natural-number codes, with primitive recursive operations ... Suppose `iPRA` proves its group
identities." The operation is a body `G` (`op G a b = G(a, b)`), the neutral element is the code `num e`, and the
identities are supplied as iPRA-provable schemas (`Assoc`, `Comm`, `IdL`), exactly as in the hypothesis of the
theorem. Natural multiples are defined by primitive recursion: `0·X = e`, `(n + 1)·X = n·X + X` (`smul`).

* `smul_zero`, `smul_succ`: the recursion equations;
* `swap4`: `(a + b) + (c + d) = (a + c) + (b + d)`;
* `smul_op`: `n·(X + Y) = n·X + n·Y`;
* `smul_add`: `(a + b)·X = a·X + b·X`;
* `smul_mul`: `(b a)·X = a·(b·X)`.
-/

namespace LeanProofs.IPRA.Foundations.AbelianCodes

open_ipra exports

/-- The group operation `G(a, b)`. -/
abbrev op (G : PTm 2) {n : ℕ} (a b : PTm n) : PTm n := inst2 G a b

/-- Associativity, as an iPRA-provable schema. -/
def Assoc (G : PTm 2) : Prop :=
  ∀ {n : ℕ} {Δ : List (Fm PTm n)} (a b c : PTm n), Δ ⊢[PRAAx] op G (op G a b) c ≐ op G a (op G b c)
/-- Commutativity. -/
def Comm (G : PTm 2) : Prop := ∀ {n : ℕ} {Δ : List (Fm PTm n)} (a b : PTm n), Δ ⊢[PRAAx] op G a b ≐ op G b a
/-- The neutral element `num e`. -/
def IdL (G : PTm 2) (e : ℕ) : Prop := ∀ {n : ℕ} {Δ : List (Fm PTm n)} (a : PTm n), Δ ⊢[PRAAx] op G (num e) a ≐ a

/-- Congruence of the operation. -/
theorem congrOp (G : PTm 2) {n : ℕ} {Δ : List (Fm PTm n)} {a a' b b' : PTm n} (h₁ : Δ ⊢[PRAAx] a ≐ a')
    (h₂ : Δ ⊢[PRAAx] b ≐ b') : Δ ⊢[PRAAx] op G a b ≐ op G a' b' := congrInst2 G h₁ h₂

/-- `n·X`, by `0·X = e`, `(n + 1)·X = n·X + X`. -/
abbrev smulF (G : PTm 2) (e : ℕ) : PR 2 := rec2 (num e) (inst2 G (var 1) (var 2))
abbrev smul (G : PTm 2) (e : ℕ) {n : ℕ} (k X : PTm n) : PTm n := ap2 (smulF G e) k X

variable {G : PTm 2} {e : ℕ} {n : ℕ} {Γ : List (Fm PTm n)}

theorem smul_zero (X : PTm n) : Γ ⊢[PRAAx] smul G e zero X ≐ num e := by
  simpa using rec2_zero (Γ := Γ) (num e) (inst2 G (var 1) (var 2)) X

theorem smul_succ (k X : PTm n) : Γ ⊢[PRAAx] smul G e (succ k) X ≐ op G (smul G e k X) X := by
  simpa [op] using rec2_succ (Γ := Γ) (num e) (inst2 G (var 1) (var 2)) k X

theorem congrSmul {k k' X X' : PTm n} (h₁ : Γ ⊢[PRAAx] k ≐ k') (h₂ : Γ ⊢[PRAAx] X ≐ X') :
    Γ ⊢[PRAAx] smul G e k X ≐ smul G e k' X' := congrAp2 _ h₁ h₂

theorem swap4 (hA : Assoc G) (hC : Comm G) (a b c d : PTm n) :
    Γ ⊢[PRAAx] op G (op G a b) (op G c d) ≐ op G (op G a c) (op G b d) := by
  refine (hA a b (op G c d)).eqTrans ?_
  refine .eqTrans ?_ (hA a c (op G b d)).eqSymm
  refine congrOp G (.eqRefl _) ?_
  refine (hA b c d).eqSymm.eqTrans ?_
  refine .eqTrans ?_ (hA c b d)
  exact congrOp G (hC b c) (.eqRefl _)

/-- `n·(X + Y) = n·X + n·Y`. -/
theorem smul_op (hA : Assoc G) (hC : Comm G) (hI : IdL G e) (k X Y : PTm n) :
    Γ ⊢[PRAAx] smul G e k (op G X Y) ≐ op G (smul G e k X) (smul G e k Y) := by
  have hall : Γ ⊢[PRAAx] Fm.all (smul G e (var 0) (op G (Syn.shift X) (Syn.shift Y)) ≐
      op G (smul G e (var 0) (Syn.shift X)) (smul G e (var 0) (Syn.shift Y))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (smul_zero _).eqTrans ((hI (num e)).eqSymm.eqTrans (congrOp G (smul_zero _) (smul_zero _)).eqSymm)
    · simp only [Fm.subst_eq, subst_ap2, subst_inst2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine (smul_succ _ _).eqTrans ?_
      refine .eqTrans ?_ (congrOp G (smul_succ _ _) (smul_succ _ _)).eqSymm
      exact (congrOp G Prf.hyp0 (.eqRefl _)).eqTrans (swap4 hA hC _ _ _ _)
  have h2 := Prf.allE k hall
  simpa only [Fm.subst_eq, subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h2

/-- `(a + b)·X = a·X + b·X`. -/
theorem smul_add (hA : Assoc G) (hC : Comm G) (hI : IdL G e) (a b X : PTm n) :
    Γ ⊢[PRAAx] smul G e (a + b) X ≐ op G (smul G e a X) (smul G e b X) := by
  have hall : Γ ⊢[PRAAx] Fm.all (smul G e (Syn.shift a + var 0) (Syn.shift X) ≐
      op G (smul G e (Syn.shift a) (Syn.shift X)) (smul G e (var 0) (Syn.shift X))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine (congrSmul (add_zero _) (.eqRefl _)).eqTrans ?_
      exact (hI _).eqSymm.eqTrans ((hC _ _).eqTrans (congrOp G (.eqRefl _) (smul_zero _).eqSymm))
    · simp only [Fm.subst_eq, subst_ap2, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ]
      have e1 : ((smul G e (Syn.shift a + var 0) (Syn.shift X) ≐
          op G (smul G e (Syn.shift a) (Syn.shift X)) (smul G e (var 0) (Syn.shift X))) :: Γ.map Fm.shift) ⊢[PRAAx]
          Syn.shift a + succ (var 0) ≐ succ (Syn.shift a + var 0) := by ipra_ring
      refine (congrSmul e1 (.eqRefl _)).eqTrans ((smul_succ _ _).eqTrans ?_)
      refine (congrOp G Prf.hyp0 (.eqRefl _)).eqTrans ((hA _ _ _).eqTrans ?_)
      exact congrOp G (.eqRefl _) (smul_succ _ _).eqSymm
  have h2 := Prf.allE b hall
  simpa only [Fm.subst_eq, subst_ap2, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] using h2

/-- `(b a)·X = a·(b·X)`. -/
theorem smul_mul (hA : Assoc G) (hC : Comm G) (hI : IdL G e) (a b X : PTm n) :
    Γ ⊢[PRAAx] smul G e (b * a) X ≐ smul G e a (smul G e b X) := by
  have hall : Γ ⊢[PRAAx] Fm.all (smul G e (Syn.shift b * var 0) (Syn.shift X) ≐
      smul G e (var 0) (smul G e (Syn.shift b) (Syn.shift X))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_inst2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (congrSmul (mul_zero _) (.eqRefl _)).eqTrans ((smul_zero _).eqTrans (smul_zero _).eqSymm)
    · simp only [Fm.subst_eq, subst_ap2, subst_inst2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ]
      have e1 : ((smul G e (Syn.shift b * var 0) (Syn.shift X) ≐
          smul G e (var 0) (smul G e (Syn.shift b) (Syn.shift X))) :: Γ.map Fm.shift) ⊢[PRAAx]
          Syn.shift b * succ (var 0) ≐ Syn.shift b * var 0 + Syn.shift b := by ipra_ring
      refine (congrSmul e1 (.eqRefl _)).eqTrans ((smul_add hA hC hI _ _ _).eqTrans ?_)
      exact (congrOp G Prf.hyp0 (.eqRefl _)).eqTrans (smul_succ _ _).eqSymm
  have h2 := Prf.allE a hall
  simpa only [Fm.subst_eq, subst_ap2, subst_inst2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] using h2

end LeanProofs.IPRA.Foundations.AbelianCodes
