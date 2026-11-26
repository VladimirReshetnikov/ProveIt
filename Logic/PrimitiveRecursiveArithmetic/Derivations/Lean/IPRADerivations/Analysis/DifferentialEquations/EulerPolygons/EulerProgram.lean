import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Foundations.TupleRecursion
import IPRADerivations.Foundations.SignedNorms

/-!
# The exact Euler array of a rational linear system as a primitive recursive program

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, "Data, norms, and the
exact finite program" (`eq:ode-KL`, `eq:exact-euler`). The paper fixes a dimension `d` and "a particular
primitive-recursive program evaluating a matrix `B(t)` at a rational `t ∈ [0,1]`", and defines

    X_{n,0} = v,    X_{n,j+1} = X_{n,j} + (1/n) B(j/n) X_{n,j}    (0 ≤ j < n).

Here the program is an object of iPRA and its equations are derived.

* `Kernel d`: the coefficient program. Its argument is a rational `t = p/q` given by the pair `(p, q)` and one
  further parameter `x`; its value is the matrix of integer terms `B.numAt i k p q x` (signed numerators) over the
  natural term `B.denAt p q x` (a common denominator of the matrix).
* `Xn B v j n x i` and `Xd B dv j n x`: the numerator of the `i`-th component and the denominator of `X_{n,j}`,
  for the initial vector `v / dv` (`v` integer terms, `dv` a natural term). The numerators are `d` sequences defined
  by simultaneous recursion on `j` (`Foundations/TupleRecursion`, each integer coded as a pair), the denominator is
  a product. The initial vector, the mesh `n` and the parameter are arbitrary terms. The equations, in the ring of
  differences, are

      Xn(0) = v,     Xn(j+1) = n b_j Xn(j) + M_j Xn(j),          (`Xn_zero`, `Xn_succ`)
      Xd(0) = dv,    Xd(j+1) = Xd(j) (n b_j),                    (`Xd_zero`, `Xd_succ`)

  with `M_j / b_j = B(j/n)`; this is `eq:exact-euler` over the common denominator `Xd(j)`. The congruences
  `congrXn`, `congrXd` allow provably equal indices and meshes to be exchanged.
* `KBound B x K` and `LBound B x L` are the hypotheses `eq:ode-KL` as iPRA formulas, quantified over all
  arguments `0 ≤ p ≤ q`, `0 < q`: the denominator is positive and `‖B(p/q)‖ ≤ K` for the row-sum norm
  (`rowSum (B.mat p q x) i ≤ K · den`), and `‖B(p/q) − B(p'/q')‖ ≤ L |p/q − p'/q'|`, cleared of the four
  denominators. `kbound_use` and `lbound_use` instantiate them; `subst_KBound`, `subst_LBound` move them under
  substitutions, so that they can be used inside inductions.
-/

namespace LeanProofs.IPRA.Analysis.EulerProgram

open_ipra
open LeanProofs.IPRA.Foundations.TupleRecursion LeanProofs.IPRA.Foundations.SignedNorms
  LeanProofs.IPRA.Foundations.SignedCone

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Integer terms under substitution, finite conjunctions -/

theorem zt_subst_subst {m k : ℕ} (σ : Fin n → PTm m) (τ : Fin m → PTm k) (u : ZT n) :
    (u.subst σ).subst τ = u.subst fun i => Syn.subst τ (σ i) := by
  simp only [ZT.subst, Syn.subst_subst]

/-- An integer term weakened by one variable. -/
def zshift (u : ZT n) : ZT (n + 1) := u.subst fun i => var i.succ

@[simp] theorem zshift_inst (u : ZT n) (t : PTm n) : (zshift u).subst (Syn.inst t) = u := by
  show (⟨Syn.subst (Syn.inst t) (Syn.shift u.pos), Syn.subst (Syn.inst t) (Syn.shift u.neg)⟩ : ZT n) = u
  rw [Syn.subst_inst_shift, Syn.subst_inst_shift]

@[simp] theorem zshift_repl (u : ZT n) (s : PTm (n + 1)) : (zshift u).subst (repl s) = zshift u := by
  show (⟨Syn.subst (repl s) (Syn.shift u.pos), Syn.subst (repl s) (Syn.shift u.neg)⟩ : ZT (n + 1)) = _
  rw [subst_repl_shift, subst_repl_shift]; rfl

theorem subst_up_shift {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

theorem subst_vec1 {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    (fun j => Syn.subst σ ((![a] : Fin 1 → PTm n) j)) = ![Syn.subst σ a] := by
  funext j; fin_cases j; rfl

theorem subst_vec2 {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (fun j => Syn.subst σ ((![a, b] : Fin 2 → PTm n) j)) = ![Syn.subst σ a, Syn.subst σ b] := by
  funext j; fin_cases j <;> rfl

theorem subst_sumFin {m : ℕ} (σ : Fin n → PTm m) : {k : ℕ} → (f : Fin k → ZT n) →
    (ZT.sumFin f).subst σ = ZT.sumFin fun i => (f i).subst σ
  | 0, _ => by simp only [ZT.sumFin, ZT.subst_natLit]
  | k + 1, f => by
    rw [ZT.sumFin, ZT.subst_add, subst_sumFin σ fun i => f i.succ]; rfl

theorem subst_conjFin {m : ℕ} (σ : Fin n → PTm m) : {k : ℕ} → (f : Fin k → Fm PTm n) →
    (conjFin f).subst σ = conjFin fun i => (f i).subst σ
  | 0, _ => by simp only [conjFin, Fm.subst_eq, ConciseIPRA.PTm.subst_zero]
  | 1, _ => rfl
  | k + 2, f => by
    simp only [conjFin, Fm.subst_and]
    rw [subst_conjFin σ fun i : Fin (k + 1) => f i.succ]

theorem conjFin_QF : {k : ℕ} → {f : Fin k → Fm PTm n} → (∀ i, (f i).QF) → (conjFin f).QF
  | 0, _, _ => trivial
  | 1, _, h => h 0
  | _ + 2, _, h => ⟨h 0, conjFin_QF fun i => h i.succ⟩

theorem conjFin_elim : {k : ℕ} → {f : Fin k → Fm PTm n} → (Γ ⊢[PRAAx] conjFin f) → ∀ i, (Γ ⊢[PRAAx] f i)
  | 0, _, _, i => i.elim0
  | 1, _, h, i => by
    have e : i = 0 := Subsingleton.elim _ _
    subst e; exact h
  | k + 2, f, h, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Prf.andE₁ h
    · exact conjFin_elim (f := fun j : Fin (k + 1) => f j.succ) (Prf.andE₂ h) j

/-! ## The coefficient kernel -/

/-- A rational coefficient kernel of dimension `d`: a matrix of integer terms over a common natural denominator,
in the variables `0 = p`, `1 = q` (the argument `t = p/q`) and `2 =` a parameter. -/
structure Kernel (d : ℕ) where
  num : Fin d → Fin d → ZT 3
  den : PTm 3

namespace Kernel

variable (B : Kernel d)

/-- The numerator of the entry `(i, k)` of `B(p/q)`. -/
def numAt (i k : Fin d) (p q x : PTm n) : ZT n := (B.num i k).subst ![p, q, x]

/-- The common denominator of `B(p/q)`. -/
def denAt (p q x : PTm n) : PTm n := Syn.subst ![p, q, x] B.den

/-- The matrix of numerators of `B(p/q)`. -/
def mat (p q x : PTm n) : Fin d → Fin d → ZT n := fun i k => B.numAt i k p q x

/-- The matrix of numerators of `B(p/q) − B(p'/q')` over the product of the two denominators. -/
def cross (p q p' q' x : PTm n) : Fin d → Fin d → ZT n := fun i k =>
  ZT.ofNat (B.denAt p' q' x) * B.numAt i k p q x - ZT.ofNat (B.denAt p q x) * B.numAt i k p' q' x

@[simp] theorem subst_denAt {m : ℕ} (σ : Fin n → PTm m) (p q x : PTm n) :
    Syn.subst σ (B.denAt p q x) = B.denAt (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ x) := by
  simp only [denAt, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_numAt {m : ℕ} (σ : Fin n → PTm m) (i k : Fin d) (p q x : PTm n) :
    (B.numAt i k p q x).subst σ = B.numAt i k (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ x) := by
  simp only [numAt, zt_subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

/-- Provably equal arguments give equal denominators. -/
theorem congrDenAt {p p' q q' : PTm n} (x : PTm n) (hp : Γ ⊢[PRAAx] p ≐ p') (hq : Γ ⊢[PRAAx] q ≐ q') :
    Γ ⊢[PRAAx] B.denAt p q x ≐ B.denAt p' q' x :=
  Prf.eqCongr B.den fun j => by
    fin_cases j
    · exact hp
    · exact hq
    · exact .eqRefl x

/-- Provably equal arguments give equal numerators. -/
theorem congrNumAt (i k : Fin d) {p p' q q' : PTm n} (x : PTm n) (hp : Γ ⊢[PRAAx] p ≐ p')
    (hq : Γ ⊢[PRAAx] q ≐ q') : ZT.toZ Γ (B.numAt i k p q x) = ZT.toZ Γ (B.numAt i k p' q' x) := by
  have h : ∀ j : Fin 3, Γ ⊢[PRAAx] (![p, q, x] : Fin 3 → PTm n) j ≐ (![p', q', x] : Fin 3 → PTm n) j :=
    fun j => by
      fin_cases j
      · exact hp
      · exact hq
      · exact .eqRefl x
  exact ZT.toZ_eq (show Γ ⊢[PRAAx] ZT.eq (B.numAt i k p q x) (B.numAt i k p' q' x) from
    congrAdd (Prf.eqCongr (B.num i k).pos h) (Prf.eqCongr (B.num i k).neg h).eqSymm)

end Kernel

/-! ## The numerator and denominator programs -/

/-- The integer term read from a pair code. -/
def unp (c : PTm n) : ZT n := ⟨fstT c, sndT c⟩

@[simp] theorem subst_unp {m : ℕ} (σ : Fin n → PTm m) (c : PTm n) : (unp c).subst σ = unp (Syn.subst σ c) := by
  simp only [unp, ZT.subst, subst_fstT, subst_sndT]

/-- The next numerator vector `n b X + M X`, for `M / b = B(j/n)`. -/
def nextNum (B : Kernel d) (j nn x : PTm n) (X : Fin d → ZT n) (i : Fin d) : ZT n :=
  ZT.ofNat (nn * B.denAt j nn x) * X i + ZT.sumFin fun l => B.numAt i l j nn x * X l

theorem subst_nextNum {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (j nn x : PTm n) (X : Fin d → ZT n)
    (i : Fin d) :
    (nextNum B j nn x X i).subst σ =
      nextNum B (Syn.subst σ j) (Syn.subst σ nn) (Syn.subst σ x) (fun l => (X l).subst σ) i := by
  simp only [nextNum, ZT.subst_add, ZT.subst_mul, ZT.subst_ofNat, PTm.subst_mul, Kernel.subst_denAt,
    Kernel.subst_numAt, subst_sumFin]

/-- The step of the numerators: the current values are pair codes, the parameters are the mesh and the
parameter of the kernel. -/
def numStep (B : Kernel d) : Step d 2 where
  fn y s p i := pairT (nextNum B y (p 0) (p 1) (fun l => unp (s l)) i).pos
    (nextNum B y (p 0) (p 1) (fun l => unp (s l)) i).neg
  nat σ y s p i := by
    have h := subst_nextNum σ B y (p 0) (p 1) (fun l => unp (s l)) i
    simp only [subst_unp] at h
    show Syn.subst σ (pairT _ _) = pairT _ _
    rw [subst_pairT]
    exact congrArg₂ pairT (congrArg ZT.pos h) (congrArg ZT.neg h)

/-- The step of the denominator. -/
def denStep (B : Kernel d) : Step 1 2 where
  fn y s p _ := s 0 * (p 0 * B.denAt y (p 0) (p 1))
  nat σ y s p _ := by simp only [PTm.subst_mul, Kernel.subst_denAt]

/-- The pair codes of an initial vector. -/
def initCode (v : Fin d → ZT n) : Fin d → PTm n := fun l => pairT (v l).pos (v l).neg

/-- The numerator of the `i`-th component of the Euler node value `X_{nn,j}`. -/
def Xn (B : Kernel d) (v : Fin d → ZT n) (j nn x : PTm n) (i : Fin d) : ZT n :=
  unp (vrec (numStep B) i j (initCode v) ![nn, x])

/-- The denominator of the Euler node value `X_{nn,j}`. -/
def Xd (B : Kernel d) (dv j nn x : PTm n) : PTm n := vrec (denStep B) 0 j ![dv] ![nn, x]

@[simp] theorem subst_Xn {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n) (j nn x : PTm n)
    (i : Fin d) :
    (Xn B v j nn x i).subst σ =
      Xn B (fun l => (v l).subst σ) (Syn.subst σ j) (Syn.subst σ nn) (Syn.subst σ x) i := by
  simp only [Xn, subst_unp, subst_vrec, subst_vec2, initCode, subst_pairT]
  rfl

@[simp] theorem subst_Xd {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (dv j nn x : PTm n) :
    Syn.subst σ (Xd B dv j nn x) = Xd B (Syn.subst σ dv) (Syn.subst σ j) (Syn.subst σ nn) (Syn.subst σ x) := by
  simp only [Xd, subst_vrec, subst_vec2, subst_vec1]

section Equations

variable (B : Kernel d) (v : Fin d → ZT n) (dv j nn x : PTm n)

/-- `X_{n,0} = v`. -/
theorem Xn_zero (i : Fin d) : ZT.toZ Γ (Xn B v zero nn x i) = ZT.toZ Γ (v i) := by
  have h : Γ ⊢[PRAAx] vrec (numStep B) i zero (initCode v) ![nn, x] ≐ pairT (v i).pos (v i).neg :=
    vrec_zero _ i _ _
  exact ZT.toZ_eq (show Γ ⊢[PRAAx] ZT.eq (Xn B v zero nn x i) (v i) from congrAdd h.fstE h.sndE.eqSymm)

/-- The Euler step of the numerators as an integer equation. -/
theorem Xn_eq_succ (i : Fin d) :
    Γ ⊢[PRAAx] ZT.eq (Xn B v (succ j) nn x i) (nextNum B j nn x (fun l => Xn B v j nn x l) i) := by
  have h : Γ ⊢[PRAAx] vrec (numStep B) i (succ j) (initCode v) ![nn, x] ≐
      pairT (nextNum B j nn x (fun l => Xn B v j nn x l) i).pos
        (nextNum B j nn x (fun l => Xn B v j nn x l) i).neg :=
    vrec_succ _ i j _ _
  exact congrAdd h.fstE h.sndE.eqSymm

/-- `eq:exact-euler` for the numerators: `Xn(j+1) = n b_j Xn(j) + M_j Xn(j)`. -/
theorem Xn_succ (i : Fin d) :
    ZT.toZ Γ (Xn B v (succ j) nn x i) =
      𝔞 nn * 𝔞 (B.denAt j nn x) * ZT.toZ Γ (Xn B v j nn x i) +
        ∑ l, ZT.toZ Γ (B.numAt i l j nn x) * ZT.toZ Γ (Xn B v j nn x l) := by
  have t := ZT.toZ_eq (Xn_eq_succ (Γ := Γ) B v j nn x i)
  simpa only [nextNum, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_sumFin, Q.mk_mul, map_mul] using t

theorem Xd_eq_zero : Γ ⊢[PRAAx] Xd B dv zero nn x ≐ dv :=
  vrec_zero (denStep B) 0 ![dv] ![nn, x]

theorem Xd_eq_succ : Γ ⊢[PRAAx] Xd B dv (succ j) nn x ≐ Xd B dv j nn x * (nn * B.denAt j nn x) :=
  vrec_succ (denStep B) 0 j ![dv] ![nn, x]

/-- `Xd(0) = dv`. -/
theorem Xd_zero : (𝔞 (Xd B dv zero nn x) : Groth (Q Γ)) = 𝔞 dv := natEq (Xd_eq_zero B dv nn x)

/-- `Xd(j+1) = n b_j Xd(j)`. -/
theorem Xd_succ :
    (𝔞 (Xd B dv (succ j) nn x) : Groth (Q Γ)) = 𝔞 nn * 𝔞 (B.denAt j nn x) * 𝔞 (Xd B dv j nn x) := by
  have e := natEq (Xd_eq_succ (Γ := Γ) B dv j nn x)
  simp only [Q.mk_mul, map_mul] at e
  rw [e]; ring

end Equations

/-- Provably equal indices and meshes give equal numerators. -/
theorem congrXn (B : Kernel d) (v : Fin d → ZT n) {j j' nn nn' : PTm n} (x : PTm n) (i : Fin d)
    (hj : Γ ⊢[PRAAx] j ≐ j') (hn : Γ ⊢[PRAAx] nn ≐ nn') :
    ZT.toZ Γ (Xn B v j nn x i) = ZT.toZ Γ (Xn B v j' nn' x i) := by
  have h : Γ ⊢[PRAAx] vrec (numStep B) i j (initCode v) ![nn, x] ≐ vrec (numStep B) i j' (initCode v) ![nn', x] :=
    congrVrec _ i hj (fun _ => .eqRefl _) fun l => by
      fin_cases l
      · exact hn
      · exact .eqRefl _
  exact ZT.toZ_eq (show Γ ⊢[PRAAx] ZT.eq (Xn B v j nn x i) (Xn B v j' nn' x i) from
    congrAdd (congrFst h) (congrSnd h).eqSymm)

/-- Provably equal indices and meshes give equal denominators. -/
theorem congrXd (B : Kernel d) (dv : PTm n) {j j' nn nn' : PTm n} (x : PTm n)
    (hj : Γ ⊢[PRAAx] j ≐ j') (hn : Γ ⊢[PRAAx] nn ≐ nn') :
    Γ ⊢[PRAAx] Xd B dv j nn x ≐ Xd B dv j' nn' x :=
  congrVrec _ 0 hj (fun _ => .eqRefl _) fun l => by
    fin_cases l
    · exact hn
    · exact .eqRefl _

/-! ## The hypotheses `eq:ode-KL` -/

section Hypotheses

variable (B : Kernel d)

/-- `‖B(p/q)‖ ≤ K` with a positive denominator, for one argument `0 ≤ p ≤ q`, `0 < q`. -/
def KBody (p q x K : PTm n) : Fm PTm n :=
  lt zero q ⟶ le p q ⟶
    (lt zero (B.denAt p q x) ⋏ conjFin fun i => le (rowSum (B.mat p q x) i) (K * B.denAt p q x))

@[simp] theorem subst_KBody {m : ℕ} (σ : Fin n → PTm m) (p q x K : PTm n) :
    (KBody B p q x K).subst σ = KBody B (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ x) (Syn.subst σ K) := by
  simp only [KBody, Fm.subst_imp, Fm.subst_and, subst_lt, subst_le, subst_conjFin, subst_rowSum, Kernel.mat,
    Kernel.subst_numAt, Kernel.subst_denAt, PTm.subst_mul, ConciseIPRA.PTm.subst_zero]
  rfl

def KB1 (p x K : PTm n) : Fm PTm n :=
  Fm.all (KBody B (Syn.shift p) (var 0) (Syn.shift x) (Syn.shift K))

@[simp] theorem subst_KB1 {m : ℕ} (σ : Fin n → PTm m) (p x K : PTm n) :
    (KB1 B p x K).subst σ = KB1 B (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ K) := by
  simp only [KB1, Fm.subst_all, subst_KBody, subst_up_shift, Syn.subst_var, Syn.up_zero]

/-- The hypothesis `‖B(t)‖ ≤ K` of `eq:ode-KL`, for all rational arguments of the interval. -/
def KBound (x K : PTm n) : Fm PTm n := Fm.all (KB1 B (var 0) (Syn.shift x) (Syn.shift K))

@[simp] theorem subst_KBound {m : ℕ} (σ : Fin n → PTm m) (x K : PTm n) :
    (KBound B x K).subst σ = KBound B (Syn.subst σ x) (Syn.subst σ K) := by
  simp only [KBound, Fm.subst_all, subst_KB1, subst_up_shift, Syn.subst_var, Syn.up_zero]

variable {B}

theorem kbound_inst {x K : PTm n} (h : Γ ⊢[PRAAx] KBound B x K) (p q : PTm n) : Γ ⊢[PRAAx] KBody B p q x K := by
  have h1 := Prf.allE p h
  simp only [subst_KB1, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h1
  have h2 := Prf.allE q h1
  simp only [subst_KBody, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h2
  exact h2

/-- The bound `‖B(p/q)‖ ≤ K` at an argument of the interval. -/
theorem kbound_use {x K : PTm n} (h : Γ ⊢[PRAAx] KBound B x K) {p q : PTm n} (hq : Γ ⊢[PRAAx] lt zero q)
    (hp : Γ ⊢[PRAAx] le p q) :
    (Γ ⊢[PRAAx] lt zero (B.denAt p q x)) ∧ ∀ i, Γ ⊢[PRAAx] le (rowSum (B.mat p q x) i) (K * B.denAt p q x) :=
  have h' := Prf.impE (Prf.impE (kbound_inst h p q) hq) hp
  ⟨.andE₁ h', conjFin_elim (.andE₂ h')⟩

/-- The hypothesis `KBound` in the context of an induction. -/
theorem kbound_shift {x K : PTm n} (h : Γ ⊢[PRAAx] KBound B x K) :
    Γ.map Fm.shift ⊢[PRAAx] KBound B (Syn.shift x) (Syn.shift K) := by
  have a := h.shift
  simp only [Fm.shift, subst_KBound] at a
  exact a

variable (B)

/-- `‖B(p/q) − B(p'/q')‖ ≤ L |p/q − p'/q'|` for two arguments of the interval, cleared of denominators. -/
def LBody (p q p' q' x L : PTm n) : Fm PTm n :=
  lt zero q ⟶ le p q ⟶ lt zero q' ⟶ le p' q' ⟶
    conjFin fun i => le (rowSum (B.cross p q p' q' x) i * (q * q'))
      (L * (monus (p * q') (p' * q) + monus (p' * q) (p * q')) * (B.denAt p q x * B.denAt p' q' x))

@[simp] theorem subst_LBody {m : ℕ} (σ : Fin n → PTm m) (p q p' q' x L : PTm n) :
    (LBody B p q p' q' x L).subst σ =
      LBody B (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ p') (Syn.subst σ q') (Syn.subst σ x)
        (Syn.subst σ L) := by
  simp only [LBody, Fm.subst_imp, subst_lt, subst_le, subst_conjFin, subst_rowSum, Kernel.cross, ZT.subst_sub,
    ZT.subst_mul, ZT.subst_ofNat, Kernel.subst_numAt, Kernel.subst_denAt, PTm.subst_mul, PTm.subst_add,
    PTm.subst_monus, ConciseIPRA.PTm.subst_zero]
  rfl

def LB3 (p q p' x L : PTm n) : Fm PTm n :=
  Fm.all (LBody B (Syn.shift p) (Syn.shift q) (Syn.shift p') (var 0) (Syn.shift x) (Syn.shift L))

@[simp] theorem subst_LB3 {m : ℕ} (σ : Fin n → PTm m) (p q p' x L : PTm n) :
    (LB3 B p q p' x L).subst σ =
      LB3 B (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ p') (Syn.subst σ x) (Syn.subst σ L) := by
  simp only [LB3, Fm.subst_all, subst_LBody, subst_up_shift, Syn.subst_var, Syn.up_zero]

def LB2 (p q x L : PTm n) : Fm PTm n :=
  Fm.all (LB3 B (Syn.shift p) (Syn.shift q) (var 0) (Syn.shift x) (Syn.shift L))

@[simp] theorem subst_LB2 {m : ℕ} (σ : Fin n → PTm m) (p q x L : PTm n) :
    (LB2 B p q x L).subst σ = LB2 B (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ x) (Syn.subst σ L) := by
  simp only [LB2, Fm.subst_all, subst_LB3, subst_up_shift, Syn.subst_var, Syn.up_zero]

def LB1 (p x L : PTm n) : Fm PTm n :=
  Fm.all (LB2 B (Syn.shift p) (var 0) (Syn.shift x) (Syn.shift L))

@[simp] theorem subst_LB1 {m : ℕ} (σ : Fin n → PTm m) (p x L : PTm n) :
    (LB1 B p x L).subst σ = LB1 B (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ L) := by
  simp only [LB1, Fm.subst_all, subst_LB2, subst_up_shift, Syn.subst_var, Syn.up_zero]

/-- The hypothesis `‖B(t) − B(s)‖ ≤ L |t − s|` of `eq:ode-KL`, for all rational arguments of the interval. -/
def LBound (x L : PTm n) : Fm PTm n := Fm.all (LB1 B (var 0) (Syn.shift x) (Syn.shift L))

@[simp] theorem subst_LBound {m : ℕ} (σ : Fin n → PTm m) (x L : PTm n) :
    (LBound B x L).subst σ = LBound B (Syn.subst σ x) (Syn.subst σ L) := by
  simp only [LBound, Fm.subst_all, subst_LB1, subst_up_shift, Syn.subst_var, Syn.up_zero]

variable {B}

theorem lbound_inst {x L : PTm n} (h : Γ ⊢[PRAAx] LBound B x L) (p q p' q' : PTm n) :
    Γ ⊢[PRAAx] LBody B p q p' q' x L := by
  have h1 := Prf.allE p h
  simp only [subst_LB1, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h1
  have h2 := Prf.allE q h1
  simp only [subst_LB2, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h2
  have h3 := Prf.allE p' h2
  simp only [subst_LB3, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h3
  have h4 := Prf.allE q' h3
  simp only [subst_LBody, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h4
  exact h4

/-- The Lipschitz bound at two arguments of the interval. -/
theorem lbound_use {x L : PTm n} (h : Γ ⊢[PRAAx] LBound B x L) {p q p' q' : PTm n}
    (hq : Γ ⊢[PRAAx] lt zero q) (hp : Γ ⊢[PRAAx] le p q) (hq' : Γ ⊢[PRAAx] lt zero q')
    (hp' : Γ ⊢[PRAAx] le p' q') (i : Fin d) :
    Γ ⊢[PRAAx] le (rowSum (B.cross p q p' q' x) i * (q * q'))
      (L * (monus (p * q') (p' * q) + monus (p' * q) (p * q')) * (B.denAt p q x * B.denAt p' q' x)) :=
  conjFin_elim (Prf.impE (Prf.impE (Prf.impE (Prf.impE (lbound_inst h p q p' q') hq) hp) hq') hp') i

/-- The hypothesis `LBound` in the context of an induction. -/
theorem lbound_shift {x L : PTm n} (h : Γ ⊢[PRAAx] LBound B x L) :
    Γ.map Fm.shift ⊢[PRAAx] LBound B (Syn.shift x) (Syn.shift L) := by
  have a := h.shift
  simp only [Fm.shift, subst_LBound] at a
  exact a

end Hypotheses

end LeanProofs.IPRA.Analysis.EulerProgram
