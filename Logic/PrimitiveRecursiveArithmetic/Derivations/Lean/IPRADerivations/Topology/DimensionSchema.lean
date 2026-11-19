import IPRADerivations.Topology.DimensionRational
import IPRADerivations.Topology.CollisionScales
import IPRADerivations.DiophantineNumberTheory.FLTMultiples

/-!
# The arithmetic dimension schema (`dimension_invariance_ipra`, `thm:schema`)

Packet: `topology/dimension_invariance_ipra`, `thm:schema`: "For each fixed primitive recursive
`A, μ`, iPRA proves that output validity and `eq:U`, `eq:I` imply `d ≤ m`." Here for every source
dimension `D = d' + 1`, every `m < D` (for `D ≤ m` there is nothing to prove) and all terms `A, μ`.

Coding. A rational point `q ∈ C_D` is a list `x` whose entries `x_0, …, x_{D−1}` are the numerators
over the common denominator `den x = fstT (tl D x)`; `valid x` says `den x ≥ 1` and `x_i ≤ den x`.
The output `A(q, p)` has the entries `(P_j − Q_j)/(R_j + 1)` with `P_j = AP j (x, p)` etc., so every
output is a valid rational tuple. With the cross terms of `Foundations/RationalFloors`
(`oGap = |X − Y|`, `oDen = (R_j(x)+1)(R_j(x')+1)`):

* `eq:U` (`Uhyp`): for all `x, x', k, p`, `valid x → valid x' → ‖q − q'‖ ≤ 2^{−μ(k)} →
  dist(A(q, p), A(q', p)) ≤ 2^{−k} + 2^{1−p}`, cleared of denominators:
  `2^{μ(k)} |x_i den x' − x'_i den x| ≤ den x · den x'` for every `i` (`srcSum`) and
  `2^{k+p} oGap ≤ (2^p + 2^{k+1}) oDen` for every `j` (`outU`);
* `eq:I` (`Ihyp a`): for all `x, x', p`, `valid x → valid x' →
  dist(A(q, p), A(q', p)) + 2^{1−p} < 2^{−a} → ‖q − q'‖ ≤ 1/2`, that is
  `2^{a+p} oGap + 2^{a+1} oDen < 2^p oDen` for every `j` (`outI`) implies `srcSum` with `2^1`.

`dimension_schema`: `iPRA ⊢ ∀ a. eq:U → eq:I(a) → ⊥`. The proof is the packet's. With
`k = a + d + 3`, `p = k + 1` (`eq:scales`, with `d = D`), `N = 2^{μ(k)}` and `h = 2^{−a−1}`, the
sampled table `F(v) = A(v/N, p)` on `G_D(N)` (`Pt`, `Qt`, `Rt`: the grid point `v` is itself the
code of `v/N`) satisfies the strict `eq:small` by `eq:U` (`small_from_U`: Kuhn vertices are
`2^{−μ(k)}`-close, and `2^{1−k} < h/D` since `D < 2^{D}`, `small_arith`) and `eq:sep` by `eq:I`
(`sep_from_I`: if every entry of a lower/upper-face pair were `h`-close, `eq:I` would give
`‖q − q'‖ ≤ 1/2` although the pair is at distance `1`, `sep_arith`). `DimensionRational.rat_no_table`
gives the contradiction. The real-variable reading (`thm:collision`, `cor:dimension`) is not part of
this module.
-/

namespace LeanProofs.IPRA.Topology.DimensionSchema

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.GridSums
open LeanProofs.IPRA.Foundations.TermSums
open LeanProofs.IPRA.Foundations.BoundedCases
open LeanProofs.IPRA.Foundations.RationalFloors
open LeanProofs.IPRA.Topology.KuhnSimplices
open LeanProofs.IPRA.Topology.SpernerCube
open LeanProofs.IPRA.Topology.StaggeredCells (near dist)
open LeanProofs.IPRA.Topology.StaggeredGrids (fprod_one)
open LeanProofs.IPRA.Topology.DimensionUnits (dist_of_add dist_comm)
open LeanProofs.IPRA.Topology.DimensionOccupancy
open LeanProofs.IPRA.Topology.DimensionObstruction
open LeanProofs.IPRA.Topology.DimensionRational
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open LeanProofs.IPRA.Topology.CollisionScales (lt_pw_two)
open Equiv

set_option autoImplicit false

variable {n : ℕ}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Arithmetic with powers of two as atoms -/

section Arith

variable {Γ : List (Fm PTm n)}

/-- `eq:smallbound`: `2^{k+p} G ≤ (2^p + 2^{k+1}) RR` with `p = k + 1`, `2^k = 2^a · 16 · 2^{d'}` and
`d' < 2^{d'}` give `D · 2^{a+1} · G < RR`. -/
theorem small_arith {G RR K T F P2p P2k1 P2kp w c r : PTm n} (d' : ℕ)
    (hU : Γ ⊢[PRAAx] (P2p + P2k1) * RR ≐ P2kp * G + w)
    (hp : Γ ⊢[PRAAx] P2p ≐ K * two) (hk1 : Γ ⊢[PRAAx] P2k1 ≐ K * two) (hkp : Γ ⊢[PRAAx] P2kp ≐ K * (K * two))
    (hK : Γ ⊢[PRAAx] K ≐ T * (F * two * two * two * two)) (hF : Γ ⊢[PRAAx] F ≐ succ (num d') + c)
    (hKpos : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hRR : Γ ⊢[PRAAx] RR ≐ succ r) :
    Γ ⊢[PRAAx] lt (num (d' + 1) * (T * two) * G) RR := by
  -- step 1: `K G ≤ 2 RR`
  have h1 : Γ ⊢[PRAAx] le (K * G) (two * RR) := by
    refine .orE (lt_or_le (two * RR) (K * G)) ?_ Prf.hyp0
    let Δ : List (Fm PTm n) := lt (two * RR) (K * G) :: Γ
    have eU := natEq (Γ := Δ) hU.wk
    have ep := natEq (Γ := Δ) hp.wk
    have ek1 := natEq (Γ := Δ) hk1.wk
    have ekp := natEq (Γ := Δ) hkp.wk
    have ez := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
    have eκ := natEq (Γ := Δ) hKpos.wk
    refine .botE _ (succ_ne_zero (a := pred K + pred K + one + two * K * monus (K * G) (succ (two * RR)) + w) ?_)
    apply deriveNat; ipra_simps
    linear_combination -(eU - 𝔞 RR * ep - 𝔞 RR * ek1 + 𝔞 G * ekp) - (2 * 𝔞 K) * ez - 2 * eκ
  -- step 2: `D · 2T · G < RR`
  refine .orE (lt_or_le (num (d' + 1) * (T * two) * G) RR) Prf.hyp0 ?_
  let Δ : List (Fm PTm n) := le RR (num (d' + 1) * (T * two) * G) :: Γ
  have e1 := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
  have e2 := natEq (eq_add_of_le (Γ := Δ) h1.wk)
  have eK := natEq (Γ := Δ) hK.wk
  have eF := natEq (Γ := Δ) hF.wk
  have e3 := natEq (Γ := Δ) hRR.wk
  refine .botE _ (succ_ne_zero (a := num 6 * r + num 8 * monus (num (d' + 1) * (T * two) * G) RR +
    num 16 * T * c * G + monus (two * RR) (K * G) + num 5) ?_)
  apply deriveNat; ipra_simps; push_cast at *
  linear_combination -e2 - 𝔞 G * eK - (16 * 𝔞 T * 𝔞 G) * eF - 8 * e1 - 6 * e3

/-- `G/RR < 2^{−a−1}` gives `G/RR + 2^{1−p} < 2^{−a}` for `p = a + d' + 5`:
`2^{a+p} G + 2^{a+1} RR < 2^p RR`. -/
theorem sep_arith {G RR T F E P2p P2ap P2a1 e c : PTm n} (d' : ℕ)
    (hRR : Γ ⊢[PRAAx] RR ≐ succ (T * two * G) + e) (hT : Γ ⊢[PRAAx] T ≐ succ (pred T))
    (hE : Γ ⊢[PRAAx] E ≐ F * two * two * two * two) (hF : Γ ⊢[PRAAx] F ≐ succ (num d') + c)
    (hp : Γ ⊢[PRAAx] P2p ≐ T * E * two) (hap : Γ ⊢[PRAAx] P2ap ≐ T * P2p) (ha1 : Γ ⊢[PRAAx] P2a1 ≐ T * two) :
    Γ ⊢[PRAAx] lt (P2ap * G + P2a1 * RR) (P2p * RR) := by
  let φ : PTm n := num d' + c
  refine le_of_eq_add (d := two * T * T * G * (num 16 * φ + num 14) + num 32 * T * φ + num 30 * pred T + num 29 +
    two * T * e * (num 16 * φ + num 15)) ?_
  have eRR := natEq hRR
  have eT := natEq hT
  have eE := natEq hE
  have eF := natEq hF
  have ep := natEq hp
  have eap := natEq hap
  have ea1 := natEq ha1
  apply deriveNat; simp only [φ]; ipra_simps
  rw [eap, ea1, ep, eE, eF, eRR, eT]
  push_cast; ring

/-- `2 · (N N) ≤ N N` is impossible for `N ≥ 1`. -/
theorem double_absurd {N X : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hX : Γ ⊢[PRAAx] X ≐ N * N)
    (h : Γ ⊢[PRAAx] le (two * X) X) : Γ ⊢[PRAAx] Fm.bot := by
  have e := natEq (eq_add_of_le h)
  have eX := natEq hX
  have eN := natEq hN
  refine succ_ne_zero (a := pred N * pred N + two * pred N + monus X (two * X)) ?_
  apply deriveNat; ipra_simps
  linear_combination -e - eX - (𝔞 N + 𝔞 (pred N) + 1) * eN

end Arith

/-! ## Rational points, outputs and the two hypotheses -/

section Hyps

variable (d' m : ℕ) (AP AQ AR : Fin m → PTm 2) (μ : PTm 1)

/-- The common denominator of a point code. -/
def den (x : PTm n) : PTm n := fstT (tl (d' + 1) x)

/-- `x` codes a point of `C_D ∩ ℚ^D`. -/
def valid (x : PTm n) : Fm PTm n := le one (den d' x) ⋏ (bsum (d' + 1) x (tl (d' + 1) x) ≐ zero)

/-- `Σ_i (2^K |x_i den x' − x'_i den x| ∸ den x den x')`: zero iff `‖q − q'‖ ≤ 2^{−K}`. -/
def srcSum (x x' K : PTm n) : PTm n :=
  fsum (d' + 1) (fun i => monus (pw two K * dist (proj i.val x * den d' x') (proj i.val x' * den d' x))
    (den d' x * den d' x'))

/-- The output entry `P_j(x, p)`. -/
def oP (j : Fin m) (x p : PTm n) : PTm n := Syn.subst ![x, p] (AP j)
def oQ (j : Fin m) (x p : PTm n) : PTm n := Syn.subst ![x, p] (AQ j)
def oR (j : Fin m) (x p : PTm n) : PTm n := Syn.subst ![x, p] (AR j)

/-- `|X − Y|` for the outputs at `x, x'`. -/
def oGap (j : Fin m) (x x' p : PTm n) : PTm n :=
  dist (crossX (oP m AP j x p) (oQ m AQ j x p) (oR m AR j x p) (oP m AP j x' p) (oQ m AQ j x' p) (oR m AR j x' p))
    (crossY (oP m AP j x p) (oQ m AQ j x p) (oR m AR j x p) (oP m AP j x' p) (oQ m AQ j x' p) (oR m AR j x' p))

/-- `(R_j(x) + 1)(R_j(x') + 1)`. -/
def oDen (j : Fin m) (x x' p : PTm n) : PTm n := succ (oR m AR j x p) * succ (oR m AR j x' p)

/-- `eq:U`, cleared: `Σ_j (2^{k+p} oGap ∸ (2^p + 2^{k+1}) oDen)`. -/
def outU (x x' k p : PTm n) : PTm n :=
  fsum m (fun j => monus (pw two (k + p) * oGap m AP AQ AR j x x' p) ((pw two p + pw two (succ k)) * oDen m AR j x x' p))

/-- `eq:I`, cleared: `Σ_j ((2^{a+p} oGap + 2^{a+1} oDen + 1) ∸ 2^p oDen)`. -/
def outI (x x' p a : PTm n) : PTm n :=
  fsum m (fun j => monus (succ (pw two (a + p) * oGap m AP AQ AR j x x' p + pw two (succ a) * oDen m AR j x x' p))
    (pw two p * oDen m AR j x x' p))

def UBody (x x' k p : PTm n) : Fm PTm n :=
  valid d' x ⟶ (valid d' x' ⟶ ((srcSum d' x x' (Syn.subst ![k] μ) ≐ zero) ⟶ (outU m AP AQ AR x x' k p ≐ zero)))

def IBody (x x' p a : PTm n) : Fm PTm n :=
  valid d' x ⟶ (valid d' x' ⟶ ((outI m AP AQ AR x x' p a ≐ zero) ⟶ (srcSum d' x x' one ≐ zero)))

/-- `eq:U` for `A`, `μ`. -/
def Uhyp : Fm PTm n :=
  Fm.all (Fm.all (Fm.all (Fm.all (UBody d' m AP AQ AR μ (Syn.var 3) (Syn.var 2) (Syn.var 1) (Syn.var 0)))))

/-- `eq:I` for `A` with the parameter `a`. -/
def Ihyp (a : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (Fm.all (IBody d' m AP AQ AR (Syn.var 2) (Syn.var 1) (Syn.var 0)
    (Syn.shift (Syn.shift (Syn.shift a))))))

@[simp] theorem subst_den {k : ℕ} (σ : Fin n → PTm k) (x : PTm n) :
    Syn.subst σ (den d' x) = den d' (Syn.subst σ x) := by simp [den]

@[simp] theorem subst_valid {k : ℕ} (σ : Fin n → PTm k) (x : PTm n) :
    (valid d' x).subst σ = valid d' (Syn.subst σ x) := by simp [valid]

@[simp] theorem subst_srcSum {k : ℕ} (σ : Fin n → PTm k) (x x' K : PTm n) :
    Syn.subst σ (srcSum d' x x' K) = srcSum d' (Syn.subst σ x) (Syn.subst σ x') (Syn.subst σ K) := by
  simp [srcSum]

theorem subst_two_vec {k : ℕ} (σ : Fin n → PTm k) (x p : PTm n) (t : PTm 2) :
    Syn.subst σ (Syn.subst ![x, p] t) = Syn.subst ![Syn.subst σ x, Syn.subst σ p] t := by
  simp only [Syn.subst_subst]; congr 1; funext i; fin_cases i <;> rfl

@[simp] theorem subst_oP {k : ℕ} (σ : Fin n → PTm k) (j : Fin m) (x p : PTm n) :
    Syn.subst σ (oP m AP j x p) = oP m AP j (Syn.subst σ x) (Syn.subst σ p) := subst_two_vec σ x p _
@[simp] theorem subst_oQ {k : ℕ} (σ : Fin n → PTm k) (j : Fin m) (x p : PTm n) :
    Syn.subst σ (oQ m AQ j x p) = oQ m AQ j (Syn.subst σ x) (Syn.subst σ p) := subst_two_vec σ x p _
@[simp] theorem subst_oR {k : ℕ} (σ : Fin n → PTm k) (j : Fin m) (x p : PTm n) :
    Syn.subst σ (oR m AR j x p) = oR m AR j (Syn.subst σ x) (Syn.subst σ p) := subst_two_vec σ x p _

@[simp] theorem subst_outU {k' : ℕ} (σ : Fin n → PTm k') (x x' k p : PTm n) :
    Syn.subst σ (outU m AP AQ AR x x' k p) =
      outU m AP AQ AR (Syn.subst σ x) (Syn.subst σ x') (Syn.subst σ k) (Syn.subst σ p) := by
  simp [outU, oGap, oDen]

@[simp] theorem subst_outI {k' : ℕ} (σ : Fin n → PTm k') (x x' p a : PTm n) :
    Syn.subst σ (outI m AP AQ AR x x' p a) =
      outI m AP AQ AR (Syn.subst σ x) (Syn.subst σ x') (Syn.subst σ p) (Syn.subst σ a) := by
  simp [outI, oGap, oDen]

theorem subst_mu {k' : ℕ} (σ : Fin n → PTm k') (k : PTm n) :
    Syn.subst σ (Syn.subst ![k] μ) = Syn.subst ![Syn.subst σ k] μ := by
  simp only [Syn.subst_subst]; congr 1; funext i; fin_cases i; rfl

@[simp] theorem subst_UBody {k' : ℕ} (σ : Fin n → PTm k') (x x' k p : PTm n) :
    (UBody d' m AP AQ AR μ x x' k p).subst σ =
      UBody d' m AP AQ AR μ (Syn.subst σ x) (Syn.subst σ x') (Syn.subst σ k) (Syn.subst σ p) := by
  simp [UBody, subst_mu]

@[simp] theorem subst_IBody {k' : ℕ} (σ : Fin n → PTm k') (x x' p a : PTm n) :
    (IBody d' m AP AQ AR x x' p a).subst σ =
      IBody d' m AP AQ AR (Syn.subst σ x) (Syn.subst σ x') (Syn.subst σ p) (Syn.subst σ a) := by
  simp [IBody]

@[simp] theorem subst_Uhyp {k' : ℕ} (σ : Fin n → PTm k') :
    (Uhyp d' m AP AQ AR μ : Fm PTm n).subst σ = Uhyp d' m AP AQ AR μ := by
  simp [Uhyp, Syn.up]

@[simp] theorem subst_Ihyp {k' : ℕ} (σ : Fin n → PTm k') (a : PTm n) :
    (Ihyp d' m AP AQ AR a).subst σ = Ihyp d' m AP AQ AR (Syn.subst σ a) := by
  simp [Ihyp, subst_up_shift', Syn.up]

theorem U_at {Γ : List (Fm PTm n)} (h : Γ ⊢[PRAAx] Uhyp d' m AP AQ AR μ) (x x' k p : PTm n) :
    Γ ⊢[PRAAx] UBody d' m AP AQ AR μ x x' k p := by
  have a1 := Prf.allE x h
  simp only [Fm.subst_all, subst_UBody] at a1
  have a2 := Prf.allE x' a1
  simp only [Fm.subst_all, subst_UBody] at a2
  have a3 := Prf.allE k a2
  simp only [Fm.subst_all, subst_UBody] at a3
  have a4 := Prf.allE p a3
  simp only [subst_UBody] at a4
  simpa [Syn.up, Syn.subst_inst_shift, subst_up_shift'] using a4

theorem I_at {Γ : List (Fm PTm n)} {a : PTm n} (h : Γ ⊢[PRAAx] Ihyp d' m AP AQ AR a) (x x' p : PTm n) :
    Γ ⊢[PRAAx] IBody d' m AP AQ AR x x' p a := by
  have a1 := Prf.allE x h
  simp only [Fm.subst_all, subst_IBody] at a1
  have a2 := Prf.allE x' a1
  simp only [Fm.subst_all, subst_IBody] at a2
  have a3 := Prf.allE p a2
  simp only [subst_IBody] at a3
  simpa [Syn.up, Syn.subst_inst_shift, subst_up_shift'] using a3

end Hyps

/-! ## The sampled table -/

section Sample

variable (d' m : ℕ) (AP AQ AR : Fin m → PTm 2) (μ : PTm 1)

/-- `k = a + d + 3` with `d = D = d' + 1`. -/
def kOf (a : PTm n) : PTm n := a + num (d' + 4)

/-- The base `⟨2^{μ(k)}, a⟩`. -/
def bOf (a : PTm n) : PTm n := pairT (pw two (Syn.subst ![kOf d' a] μ)) a

/-- The precision `p = k + 1`, read from a base. -/
def pOf (c : PTm n) : PTm n := succ (kOf d' (sndT c))

/-- The sampled entries `F_j(v) = A_j(v/N, p)` (the grid point `v` codes `v/N`). -/
def Pt (j : Fin m) : PTm 1 := Syn.subst ![Syn.var 0, pOf d' (tl (d' + 1) (Syn.var 0))] (AP j)
def Qt (j : Fin m) : PTm 1 := Syn.subst ![Syn.var 0, pOf d' (tl (d' + 1) (Syn.var 0))] (AQ j)
def Rt (j : Fin m) : PTm 1 := Syn.subst ![Syn.var 0, pOf d' (tl (d' + 1) (Syn.var 0))] (AR j)

/-- `h = 1/2^{a+1}`: `h₁ = 0`, `h₂ = 2^{a+1} − 1`. -/
def hnS : PTm 1 := zero
def hdS : PTm 1 := pred (pw two (succ (sndT (Syn.var 0))))

@[simp] theorem subst_kOf {k : ℕ} (σ : Fin n → PTm k) (a : PTm n) :
    Syn.subst σ (kOf d' a) = kOf d' (Syn.subst σ a) := by simp [kOf]

@[simp] theorem subst_bOf {k : ℕ} (σ : Fin n → PTm k) (a : PTm n) :
    Syn.subst σ (bOf d' μ a) = bOf d' μ (Syn.subst σ a) := by
  simp [bOf, subst_mu]

@[simp] theorem subst_pOf {k : ℕ} (σ : Fin n → PTm k) (c : PTm n) :
    Syn.subst σ (pOf d' c) = pOf d' (Syn.subst σ c) := by simp [pOf]

theorem col_sample (t : PTm 2) (u : PTm n) :
    col (Syn.subst ![Syn.var 0, pOf d' (tl (d' + 1) (Syn.var 0))] t) u =
      Syn.subst ![u, pOf d' (tl (d' + 1) u)] t := by
  simp only [col, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp

variable {Γ : List (Fm PTm n)} {a : PTm n}

theorem pOf_base {u : PTm n} (hu : Γ ⊢[PRAAx] tl (d' + 1) u ≐ bOf d' μ a) :
    Γ ⊢[PRAAx] pOf d' (tl (d' + 1) u) ≐ pOf d' (bOf d' μ a) :=
  congrSucc (congrAdd (congrSnd hu) (.eqRefl _))

theorem pOf_eq : Γ ⊢[PRAAx] pOf d' (bOf d' μ a) ≐ succ (kOf d' a) :=
  congrSucc (congrAdd (snd_pair _ _) (.eqRefl _))

/-- The sampled value at a grid point equals the output at the precision `p`. -/
theorem sample_eq (t : PTm 2) {u : PTm n} (hu : Γ ⊢[PRAAx] tl (d' + 1) u ≐ bOf d' μ a) :
    Γ ⊢[PRAAx] col (Syn.subst ![Syn.var 0, pOf d' (tl (d' + 1) (Syn.var 0))] t) u ≐
      Syn.subst ![u, succ (kOf d' a)] t := by
  rw [col_sample]
  exact Prf.eqCongr (Ax := PRAAx) t (σ := ![u, pOf d' (tl (d' + 1) u)]) (σ' := ![u, succ (kOf d' a)])
    (fun i => by fin_cases i; exacts [.eqRefl _, (pOf_base d' μ hu).eqTrans (pOf_eq d' μ)])

theorem crossDist_congr {Pu Qu Ru Pv Qv Rv Pu' Qu' Ru' Pv' Qv' Rv' : PTm n}
    (h1 : Γ ⊢[PRAAx] Pu ≐ Pu') (h2 : Γ ⊢[PRAAx] Qu ≐ Qu') (h3 : Γ ⊢[PRAAx] Ru ≐ Ru')
    (h4 : Γ ⊢[PRAAx] Pv ≐ Pv') (h5 : Γ ⊢[PRAAx] Qv ≐ Qv') (h6 : Γ ⊢[PRAAx] Rv ≐ Rv') :
    Γ ⊢[PRAAx] dist (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv) ≐
      dist (crossX Pu' Qu' Ru' Pv' Qv' Rv') (crossY Pu' Qu' Ru' Pv' Qv' Rv') :=
  congrDist (congrAdd (congrMul h1 (congrSucc h6)) (congrMul h5 (congrSucc h3)))
    (congrAdd (congrMul h4 (congrSucc h3)) (congrMul h2 (congrSucc h6)))

/-- The gap of the sampled table is the output gap at precision `p`. -/
theorem gap_eq (j : Fin m) {u v : PTm n} (hu : Γ ⊢[PRAAx] tl (d' + 1) u ≐ bOf d' μ a)
    (hv : Γ ⊢[PRAAx] tl (d' + 1) v ≐ bOf d' μ a) :
    Γ ⊢[PRAAx] gap m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) j u v ≐ oGap m AP AQ AR j u v (succ (kOf d' a)) :=
  crossDist_congr (sample_eq d' μ (AP j) hu) (sample_eq d' μ (AQ j) hu) (sample_eq d' μ (AR j) hu)
    (sample_eq d' μ (AP j) hv) (sample_eq d' μ (AQ j) hv) (sample_eq d' μ (AR j) hv)

theorem thr_eq (j : Fin m) {u v : PTm n} (hu : Γ ⊢[PRAAx] tl (d' + 1) u ≐ bOf d' μ a)
    (hv : Γ ⊢[PRAAx] tl (d' + 1) v ≐ bOf d' μ a) :
    Γ ⊢[PRAAx] thr m (Rt d' m AR) hnS j u v (bOf d' μ a) ≐ oDen m AR j u v (succ (kOf d' a)) := by
  have h0 : col hnS (bOf d' μ a) = zero := by simp [col, hnS]
  unfold thr; rw [h0]
  exact (one_mul _).eqTrans (congrMul (congrSucc (sample_eq d' μ (AR j) hu)) (congrSucc (sample_eq d' μ (AR j) hv)))

/-- `h₂ + 1 = 2^{a+1}`. -/
theorem hd_eq : Γ ⊢[PRAAx] succ (col hdS (bOf d' μ a)) ≐ pw two a * two := by
  have e : Γ ⊢[PRAAx] succ (col hdS (bOf d' μ a)) ≐ pw two (succ (sndT (bOf d' μ a))) := by
    simp only [col, hdS, Syn.subst_var, Matrix.cons_val_zero, PTm.subst_pred, subst_ap2, subst_sndT,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    exact (pw_pos one _).eqSymm
  exact e.eqTrans ((congrAp2 powF (congrSucc (snd_pair _ _)) (.eqRefl _)).eqTrans (pw_succ two a))

theorem N_pos : Γ ⊢[PRAAx] pw two (Syn.subst ![kOf d' a] μ) ≐ succ (pred (pw two (Syn.subst ![kOf d' a] μ))) :=
  pw_pos one _

/-- A grid point over `⟨N, a⟩` is a valid point code with denominator `N`. -/
theorem den_eq {u : PTm n} (hu : GridPt (d' + 1) Γ (bOf d' μ a) u) :
    Γ ⊢[PRAAx] den d' u ≐ pw two (Syn.subst ![kOf d' a] μ) :=
  (congrFst hu.tl).eqTrans (fst_pair _ _)

theorem valid_grid {u : PTm n} (hu : GridPt (d' + 1) Γ (bOf d' μ a) u) : Γ ⊢[PRAAx] valid d' u := by
  refine .andI ?_ ?_
  · refine le_congr (.eqRefl _) (den_eq d' μ hu).eqSymm ?_
    exact le_congr (.eqRefl _) (N_pos d' μ).eqSymm ((succ_monus_succ _ _).eqTrans (zero_monus _))
  · exact (fsum_congr (fun q => congrMonus (.eqRefl _) (congrFst hu.tl))).eqTrans hu.bound

end Sample

/-! ## `eq:U` gives the small-simplex condition -/

section Small

variable (d' m : ℕ) (AP AQ AR : Fin m → PTm 2) (μ : PTm 1)

/-- Two vertices of a Kuhn simplex: `2^{μ} |x_i N − y_i N| ≤ N N` when `den = N = 2^{μ}`. -/
theorem vert_close {Γ : List (Fm PTm n)} {N Mx My : PTm n} (hx : Γ ⊢[PRAAx] Mx ≐ N) (hy : Γ ⊢[PRAAx] My ≐ N)
    (s t : Bool) (z : PTm n) :
    Γ ⊢[PRAAx] monus (N * dist (bump s z * My) (bump t z * Mx)) (Mx * My) ≐ zero := by
  have hd : Γ ⊢[PRAAx] le (dist (bump s z * N) (bump t z * N)) N := by
    cases s <;> cases t
    · exact le_congr ((congrAdd (monus_self _) (monus_self _)).eqTrans (add_zero _)).eqSymm (.eqRefl _) (zero_le _)
    · refine le_congr (dist_comm _ _) (.eqRefl _) (le_congr (dist_of_add ?_).eqSymm (.eqRefl _) (le_refl _))
      apply deriveNat; simp only [bump]; ipra_simps; ring
    · refine le_congr (dist_of_add ?_).eqSymm (.eqRefl _) (le_refl _)
      apply deriveNat; simp only [bump]; ipra_simps; ring
    · exact le_congr ((congrAdd (monus_self _) (monus_self _)).eqTrans (add_zero _)).eqSymm (.eqRefl _) (zero_le _)
  have hd' := le_congr (congrDist (congrMul (.eqRefl _) hy.eqSymm) (congrMul (.eqRefl _) hx.eqSymm)) (.eqRefl _) hd
  have hm : Γ ⊢[PRAAx] le (N * dist (bump s z * My) (bump t z * Mx)) (N * N) := le_mul_mono_left N hd'
  exact le_congr (.eqRefl _) (congrMul hx hy).eqSymm hm
  where
    le_mul_mono_left {Δ : List (Fm PTm n)} (c : PTm n) {p q : PTm n} (h : Δ ⊢[PRAAx] le p q) :
        Δ ⊢[PRAAx] le (c * p) (c * q) := by
      refine le_of_eq_add (d := c * monus q p) ?_
      have e := natEq (eq_add_of_le h)
      apply deriveNat; ipra_simps; linear_combination 𝔞 c * e

/-- `2^{d'+4} = 2^{d'} · 16`. -/
theorem pw16 {Γ : List (Fm PTm n)} (d' : ℕ) :
    Γ ⊢[PRAAx] pw two (num (d' + 4)) ≐ pw two (num d') * two * two * two * two :=
  (pw_succ two (num (d' + 3))).eqTrans (congrMul ((pw_succ two (num (d' + 2))).eqTrans
    (congrMul ((pw_succ two (num (d' + 1))).eqTrans (congrMul (pw_succ two (num d')) (.eqRefl _)))
      (.eqRefl _))) (.eqRefl _))

theorem pw_F {Γ : List (Fm PTm n)} (d' : ℕ) :
    Γ ⊢[PRAAx] pw two (num d') ≐ succ (num d') + monus (pw two (num d')) (succ (num d')) :=
  eq_add_of_le (lt_pw_two (num d'))

/-- `eq:U` gives the strict small-simplex condition at a base point. -/
theorem small_point_U {Γ : List (Fm PTm n)} {a a0 : PTm n} (hU : Γ ⊢[PRAAx] Uhyp d' m AP AQ AR μ)
    (h₁ : Γ ⊢[PRAAx] a0 ≐ canon (d' + 1) (bOf d' μ a) a0) (h₂ : Γ ⊢[PRAAx] bsumLt (d' + 1) a0 (bOf d' μ a) ≐ zero) :
    Γ ⊢[PRAAx] rsmallSum d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS a0 (bOf d' μ a) ≐ zero := by
  have htl : Γ ⊢[PRAAx] tl (d' + 1) a0 ≐ bOf d' μ a := (congrTl (d' + 1) h₁).eqTrans (tl_canon (d' + 1) _ a0)
  have hlt : ∀ q, q < d' + 1 → (Γ ⊢[PRAAx] lt (proj q a0) (fstT (bOf d' μ a))) := fun q hq =>
    fsum_zero_elim (d' + 1) _ h₂ ⟨q, hq⟩
  have hgrid : ∀ (π : Perm (Fin (d' + 1))) (s : ℕ), GridPt (d' + 1) Γ (bOf d' μ a) (vert (d' + 1) π s a0) :=
    fun π s => by
      obtain ⟨c₁, c₂⟩ := incr_grid (d' + 1) (vbit (d' + 1) π s) a0 (bOf d' μ a) htl
        (fun q hq => le_of_lt (hlt q hq)) (fun q hq _ => hlt q hq)
      exact ⟨c₁, c₂⟩
  refine ftsum_zero (fun π => fsum_eq_zero (fun s => fsum_eq_zero (fun t => fsum_eq_zero (fun j => ?_))))
  have hus := hgrid π s.val
  have hut := hgrid π t.val
  have hsrc : Γ ⊢[PRAAx] srcSum d' (vert (d' + 1) π s.val a0) (vert (d' + 1) π t.val a0)
      (Syn.subst ![kOf d' a] μ) ≐ zero := by
    refine fsum_eq_zero (fun i => ?_)
    refine (congrMonus (congrMul (.eqRefl _) (congrDist
      (congrMul (proj_incr (d' + 1) (vbit (d' + 1) π s.val) i.val a0 i.isLt) (.eqRefl _))
      (congrMul (proj_incr (d' + 1) (vbit (d' + 1) π t.val) i.val a0 i.isLt) (.eqRefl _)))) (.eqRefl _)).eqTrans ?_
    exact vert_close (den_eq d' μ hus) (den_eq d' μ hut) _ _ _
  have hUb := U_at d' m AP AQ AR μ hU (vert (d' + 1) π s.val a0) (vert (d' + 1) π t.val a0) (kOf d' a)
    (succ (kOf d' a))
  have hout := Prf.impE (Prf.impE (Prf.impE hUb (valid_grid d' μ hus)) (valid_grid d' μ hut)) hsrc
  have hj := fsum_zero_elim m _ hout j
  have hK : Γ ⊢[PRAAx] pw two (kOf d' a) ≐ pw two a * (pw two (num d') * two * two * two * two) :=
    (pw_add two a (num (d' + 4))).eqTrans (congrMul (.eqRefl _) (pw16 d'))
  have hkp : Γ ⊢[PRAAx] pw two (kOf d' a + succ (kOf d' a)) ≐ pw two (kOf d' a) * (pw two (kOf d' a) * two) :=
    (pw_add two _ _).eqTrans (congrMul (.eqRefl _) (pw_succ two _))
  have r := small_arith d' (eq_add_of_le hj) (pw_succ two _) (pw_succ two _) hkp hK (pw_F d') (pw_pos one _)
    (denom_succ _ _)
  exact lt_congr (congrMul (congrMul (.eqRefl _) (hd_eq d' μ).eqSymm) (gap_eq d' m AP AQ AR μ j hus.tl hut.tl).eqSymm)
    (thr_eq d' m AR μ j hus.tl hut.tl).eqSymm r

theorem shift_bOf (a : PTm n) : Syn.shift (bOf d' μ a) = bOf d' μ (Syn.shift a) := by
  simp [Syn.shift]

theorem small_from_U {Γ : List (Fm PTm n)} {a : PTm n} (hU : Γ ⊢[PRAAx] Uhyp d' m AP AQ AR μ) :
    Γ ⊢[PRAAx] rhSmall d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS (bOf d' μ a) := by
  unfold rhSmall
  rw [shift_bOf]
  refine .allI (.impI (.impI ?_))
  have e := hU.shift
  simp only [Fm.shift, subst_Uhyp] at e
  exact small_point_U d' m AP AQ AR μ e.wk.wk Prf.hyp1 Prf.hyp0

end Small

/-! ## `eq:I` gives the separation condition -/

section Sep

variable (d' m : ℕ) (AP AQ AR : Fin m → PTm 2) (μ : PTm 1)

theorem sep_from_I {Γ : List (Fm PTm n)} {a u v : PTm n} {g : ℕ} (hg : g ≤ d')
    (hI : Γ ⊢[PRAAx] Ihyp d' m AP AQ AR a)
    (hu : GridPt (d' + 1) Γ (bOf d' μ a) u) (hv : GridPt (d' + 1) Γ (bOf d' μ a) v)
    (h0 : Γ ⊢[PRAAx] proj (d' - g) u ≐ zero) (hN : Γ ⊢[PRAAx] proj (d' - g) v ≐ fstT (bOf d' μ a)) :
    Γ ⊢[PRAAx] fprod m (fun j => Signum.sg (monus (thr m (Rt d' m AR) hnS j u v (bOf d' μ a))
      (succ (col hdS (bOf d' μ a)) * gap m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) j u v))) ≐ zero := by
  refine bounded_cases 1 (fun j : Fin m => Signum.sg (monus (thr m (Rt d' m AR) hnS j u v (bOf d' μ a))
      (succ (col hdS (bOf d' μ a)) * gap m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) j u v)))
    _ (fun j => le_one_monus _) (fun ρ hρ Δ' hext hκ => ?_)
  by_cases hall : ∀ j, ρ j = 1
  · refine .botE _ ?_
    -- every entry is `h`-close
    have hlt : ∀ j : Fin m, Δ' ⊢[PRAAx] lt (succ (col hdS (bOf d' μ a)) * gap m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) j u v)
        (thr m (Rt d' m AR) hnS j u v (bOf d' μ a)) := fun j => by
      have hj := hκ j
      rw [hall j] at hj
      refine .orE (lt_or_le (succ (col hdS (bOf d' μ a)) * gap m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) j u v)
        (thr m (Rt d' m AR) hnS j u v (bOf d' μ a))) Prf.hyp0 ?_
      refine .botE _ (succ_ne_zero (a := zero) ?_)
      exact hj.wk.eqSymm.eqTrans ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans Signum.sg_zero)
    have hout : Δ' ⊢[PRAAx] outI m AP AQ AR u v (succ (kOf d' a)) a ≐ zero := by
      refine fsum_eq_zero (fun j => ?_)
      have c := lt_congr (congrMul (hext _ (hd_eq d' μ)) (hext _ (gap_eq d' m AP AQ AR μ j hu.tl hv.tl)))
        (hext _ (thr_eq d' m AR μ j hu.tl hv.tl)) (hlt j)
      have hp : Δ' ⊢[PRAAx] pw two (succ (kOf d' a)) ≐ pw two a * pw two (num (d' + 4)) * two :=
        (pw_succ two _).eqTrans (congrMul (pw_add two a (num (d' + 4))) (.eqRefl _))
      exact sep_arith d' (eq_add_of_le c) (pw_pos one a) (pw16 d') (pw_F d') hp (pw_add two a _) (pw_succ two a)
    have hIb := hext _ (I_at d' m AP AQ AR hI u v (succ (kOf d' a)))
    have hsrc := Prf.impE (Prf.impE (Prf.impE hIb (hext _ (valid_grid d' μ hu))) (hext _ (valid_grid d' μ hv))) hout
    have hq := fsum_zero_elim (d' + 1) _ hsrc ⟨d' - g, by omega⟩
    -- the pair is at source distance `1`
    have hNN : Δ' ⊢[PRAAx] dist (proj (d' - g) u * den d' v) (proj (d' - g) v * den d' u) ≐
        pw two (Syn.subst ![kOf d' a] μ) * pw two (Syn.subst ![kOf d' a] μ) := by
      refine (congrDist (congrMul (hext _ h0) (hext _ (den_eq d' μ hv)))
        (congrMul ((hext _ hN).eqTrans (fst_pair _ _)) (hext _ (den_eq d' μ hu)))).eqTrans ?_
      refine (dist_comm _ _).eqTrans (dist_of_add ?_)
      apply deriveNat; ipra_simps; ring
    have hle : Δ' ⊢[PRAAx] le (two * (pw two (Syn.subst ![kOf d' a] μ) * pw two (Syn.subst ![kOf d' a] μ)))
        (pw two (Syn.subst ![kOf d' a] μ) * pw two (Syn.subst ![kOf d' a] μ)) :=
      le_congr (congrMul (pw_one two) hNN) (congrMul (hext _ (den_eq d' μ hu)) (hext _ (den_eq d' μ hv))) hq
    exact double_absurd (pw_pos one _) (.eqRefl _) hle
  · simp only [not_forall] at hall
    obtain ⟨j, hj⟩ := hall
    have h0' : ρ j = 0 := by have := hρ j; omega
    have hj' := hκ j
    rw [h0'] at hj'
    exact fprod_eq_zero j hj'

theorem sep_body_I {Γ : List (Fm PTm n)} {a u v : PTm n} {g : ℕ} (hg : g ≤ d')
    (hI : Γ ⊢[PRAAx] Ihyp d' m AP AQ AR a) :
    Γ ⊢[PRAAx] rsepBody d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS g u v (bOf d' μ a) := by
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  let b := bOf d' μ a
  let Δ : List (Fm PTm n) := (proj (d' - g) v ≐ fstT b) :: (proj (d' - g) u ≐ zero) ::
    (bsum (d' + 1) v b ≐ zero) :: (v ≐ canon (d' + 1) b v) :: (bsum (d' + 1) u b ≐ zero) ::
    (u ≐ canon (d' + 1) b u) :: Γ
  have hu : GridPt (d' + 1) Δ b u := ⟨.hyp (by simp [Δ]), .hyp (by simp [Δ])⟩
  have hv : GridPt (d' + 1) Δ b v := ⟨.hyp (by simp [Δ]), .hyp (by simp [Δ])⟩
  have h0 : Δ ⊢[PRAAx] proj (d' - g) u ≐ zero := Prf.hyp1
  have hN : Δ ⊢[PRAAx] proj (d' - g) v ≐ fstT b := Prf.hyp0
  have hI' : Δ ⊢[PRAAx] Ihyp d' m AP AQ AR a := hI.wk.wk.wk.wk.wk.wk
  exact sep_from_I d' m AP AQ AR μ hg hI' hu hv h0 hN

theorem sep_from_I_nat {Γ : List (Fm PTm n)} {a : PTm n} {g : ℕ} (hg : g ≤ d')
    (hI : Γ ⊢[PRAAx] Ihyp d' m AP AQ AR a) :
    Γ ⊢[PRAAx] rhSep d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS g (bOf d' μ a) := by
  unfold rhSep
  rw [shift_bOf, shift_bOf]
  refine .allI (.allI ?_)
  have e := hI.shift.shift
  simp only [Fm.shift, subst_Ihyp] at e
  exact sep_body_I d' m AP AQ AR μ hg e

end Sep

/-! ## The schema -/

section Schema

variable (d' m : ℕ) (AP AQ AR : Fin m → PTm 2) (μ : PTm 1)

theorem schema_core (hdm : m < d' + 1) {Γ : List (Fm PTm n)} {a : PTm n}
    (hU : Γ ⊢[PRAAx] Uhyp d' m AP AQ AR μ) (hI : Γ ⊢[PRAAx] Ihyp d' m AP AQ AR a) : Γ ⊢[PRAAx] Fm.bot :=
  rat_no_table d' m (Pt d' m AP) (Qt d' m AQ) (Rt d' m AR) hnS hdS hdm (b := bOf d' μ a)
    (fun _ hg => sep_from_I_nat d' m AP AQ AR μ hg hI) (small_from_U d' m AP AQ AR μ hU)

/-- `∀ a. eq:U → eq:I(a) → ⊥`. -/
def schemaFormula : Fm PTm 1 := Uhyp d' m AP AQ AR μ ⟶ (Ihyp d' m AP AQ AR (Syn.var 0) ⟶ Fm.bot)

/-- `thm:schema` for every source dimension `D = d' + 1`, every target dimension `m < D` and all
primitive recursive `A, μ`: iPRA proves that `eq:U` and `eq:I` (for any parameter `a`) are
contradictory, that is `D ≤ m` follows from them. -/
theorem dimension_schema (hdm : m < d' + 1) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (schemaFormula d' m AP AQ AR μ) :=
  closeUniv 1 (.impI (.impI (schema_core d' m AP AQ AR μ hdm Prf.hyp1 Prf.hyp0)))

end Schema

/-! ## Constructive dimension invariance -/

section Invariance

variable (n' m' : ℕ) (AP AQ AR : Fin (m' + 1) → PTm 2) (μ : PTm 1) (BP BQ BR : Fin (n' + 1) → PTm 2)
  (ν : PTm 1)

/-- A map `f : C_n → ℝ^m` presented by `A, μ` with inverse information at the scale `a` (variable `0`)
and a map `g : C_m → ℝ^n` presented by `B, ν` with inverse information at the scale `b`
(variable `1`). -/
def invFormula : Fm PTm 2 :=
  Uhyp n' (m' + 1) AP AQ AR μ ⟶ (Ihyp n' (m' + 1) AP AQ AR (Syn.var 0) ⟶
    (Uhyp m' (n' + 1) BP BQ BR ν ⟶ (Ihyp m' (n' + 1) BP BQ BR (Syn.var 1) ⟶ Fm.bot)))

/-- `cor:dimension`, the nontrivial implication, for positive dimensions `n = n' + 1`,
`m = m' + 1`: if `n ≠ m`, iPRA refutes the presentations `eq:U`, `eq:I` of `f` and of `g` (the
schema applied to `f` when `m < n` and to `g` when `n < m`). -/
theorem dimension_invariance (hnm : n' ≠ m') :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (invFormula n' m' AP AQ AR μ BP BQ BR ν) := by
  refine closeUniv 2 (.impI (.impI (.impI (.impI ?_))))
  rcases Nat.lt_or_gt_of_ne hnm with h | h
  · exact schema_core m' (n' + 1) BP BQ BR ν (by omega) (a := Syn.var 1) (.hyp (by simp)) (.hyp (by simp))
  · exact schema_core n' (m' + 1) AP AQ AR μ (by omega) (a := Syn.var 0) (.hyp (by simp)) (.hyp (by simp))

end Invariance

end LeanProofs.IPRA.Topology.DimensionSchema
