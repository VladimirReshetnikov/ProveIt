import IPRADerivations.Algebra.AdjugateInverse
import Mathlib.Algebra.Polynomial.Div

/-!
# Truncated power series over iPRA integers and the Lagrange fixed point

Packet: `algebra/lagrange_inversion_ipra`, `paper/lagrange_inversion_ipra.tex`, Lemma `lem:improve` ("If
`A ≡_m B`, then `S_Φ(A) ≡_{m+1} S_Φ(B)`") and Theorem `thm:fixed` ("The iterate `G = G^{(N+1)}` satisfies
`G = XΦ(G) (mod X^{N+1})`. It is the unique element of `T_N(R)` with zero constant coefficient satisfying this
equation"), for `S_Φ(A) = XΦ(A)`.

A reusable layer for formal series: a polynomial is a list of integer terms (`ZPoly`, coefficients from degree
`0`), with `add`, `smul`, `mul`, `comp` and `shiftX` (multiplication by `X`) on the syntax. `toP` evaluates it in
the polynomial ring over the ring of the context, a homomorphism for all the operations (`toP_add`, `toP_mul`,
`toP_comp`, …). Congruence modulo `X^m` is the object formula `cong m A B`, the conjunction of the coefficient
equations below `m`; it is derivable exactly when `X^m` divides `toP A − toP B` (`cong_of_dvd`, `dvd_of_cong`).
Every statement below holds for all object coefficient terms and every fixed truncation order.

* `improve` (`lem:improve`): `A ≡_m B` gives `XΦ(A) ≡_{m+1} XΦ(B)`;
* `iter_step`, `fixed` (`thm:fixed`, existence): the iterates `G^{(0)} = 0`, `G^{(k+1)} = XΦ(G^{(k)})` satisfy
  `G^{(k)} ≡_k G^{(k+1)}`, so `G^{(N+1)} ≡_{N+1} XΦ(G^{(N+1)})`;
* `unique` (`thm:fixed`, uniqueness): two solutions of `G ≡_{N+1} XΦ(G)` are congruent modulo `X^{N+1}` (their
  constant coefficients vanish automatically).
-/

namespace LeanProofs.IPRA.Algebra.TruncatedSeries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.AdjugateInverse (conjFin_elim)
open Polynomial
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A polynomial as the list of its coefficients, from degree `0`. -/
abbrev ZPoly (n : ℕ) := List (ZT n)

/-- Evaluation in the polynomial ring over the ring of the context. -/
noncomputable def toP (Γ : List (Fm PTm n)) : ZPoly n → (Groth (Q Γ))[X]
  | [] => 0
  | c :: cs => C (ZT.toZ Γ c) + X * toP Γ cs

def add : ZPoly n → ZPoly n → ZPoly n
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

def smul (c : ZT n) (p : ZPoly n) : ZPoly n := p.map (c * ·)

def mul : ZPoly n → ZPoly n → ZPoly n
  | [], _ => []
  | a :: p, q => add (smul a q) (ZT.natLit 0 :: mul p q)

/-- `Φ(A)`. -/
def comp : ZPoly n → ZPoly n → ZPoly n
  | [], _ => []
  | c :: cs, A => add [c] (mul A (comp cs A))

/-- `X A`. -/
def shiftX (A : ZPoly n) : ZPoly n := ZT.natLit 0 :: A

/-- The coefficient of degree `i`. -/
def coef (p : ZPoly n) (i : ℕ) : ZT n := p.getD i (ZT.natLit 0)

theorem toP_add (p q : ZPoly n) : toP Γ (add p q) = toP Γ p + toP Γ q := by
  induction p generalizing q with
  | nil => simp [add, toP]
  | cons a p ih =>
    cases q with
    | nil => simp [add, toP]
    | cons b q => simp only [add, toP, ih, ZT.toZ_add, map_add]; ring

theorem toP_smul (c : ZT n) (p : ZPoly n) : toP Γ (smul c p) = C (ZT.toZ Γ c) * toP Γ p := by
  induction p with
  | nil => simp [smul, toP]
  | cons a p ih =>
    simp only [smul, List.map_cons] at ih ⊢
    simp only [toP, ih, ZT.toZ_mul, map_mul]; ring

theorem toP_mul (p q : ZPoly n) : toP Γ (mul p q) = toP Γ p * toP Γ q := by
  induction p with
  | nil => simp [mul, toP]
  | cons a p ih => simp only [mul, toP_add, toP_smul, toP, ih, ZT.toZ_natLit, Nat.cast_zero, map_zero]; ring

theorem toP_comp (Φ A : ZPoly n) : toP Γ (comp Φ A) = (toP Γ Φ).comp (toP Γ A) := by
  induction Φ with
  | nil => simp [comp, toP]
  | cons c cs ih =>
    simp only [comp, toP_add, toP_mul, ih, toP, add_comp, C_comp, mul_comp, X_comp, mul_zero, add_zero]
    ring

theorem toP_shiftX (A : ZPoly n) : toP Γ (shiftX A) = X * toP Γ A := by
  simp [shiftX, toP]

theorem coeff_toP (p : ZPoly n) (i : ℕ) : (toP Γ p).coeff i = ZT.toZ Γ (coef p i) := by
  induction p generalizing i with
  | nil => simp [toP, coef]
  | cons c cs ih =>
    cases i with
    | zero => simp [toP, coef]
    | succ j => simp [toP, coef, ih j, coeff_C, coef]

/-- `A ≡ B (mod X^m)`, as the conjunction of the coefficient equations below `m`. -/
def cong (m : ℕ) (A B : ZPoly n) : Fm PTm n := conjFin fun i : Fin m => ZT.eq (coef A i) (coef B i)

theorem cong_of_dvd {m : ℕ} {A B : ZPoly n} (h : (X : (Groth (Q Γ))[X]) ^ m ∣ toP Γ A - toP Γ B) :
    Γ ⊢[PRAAx] cong m A B := by
  refine conjFin_intro fun i => ZT.derive ?_
  have hc := (X_pow_dvd_iff.mp h) i i.2
  rw [coeff_sub, coeff_toP, coeff_toP] at hc
  exact sub_eq_zero.mp hc

theorem dvd_of_cong {m : ℕ} {A B : ZPoly n} (h : Γ ⊢[PRAAx] cong m A B) :
    (X : (Groth (Q Γ))[X]) ^ m ∣ toP Γ A - toP Γ B := by
  refine X_pow_dvd_iff.mpr fun d hd => ?_
  rw [coeff_sub, coeff_toP, coeff_toP, ZT.toZ_eq (conjFin_elim h ⟨d, hd⟩), sub_self]

theorem comp_sub_dvd {R : Type*} [CommRing R] (p a b : R[X]) : a - b ∣ p.comp a - p.comp b := by
  simpa [Polynomial.comp, eval₂_eq_eval_map] using sub_dvd_eval_sub a b (p.map C)

theorem improve_dvd {R : Type*} [CommRing R] {m : ℕ} (p a b : R[X]) (h : (X : R[X]) ^ m ∣ a - b) :
    (X : R[X]) ^ (m + 1) ∣ X * p.comp a - X * p.comp b := by
  rw [← _root_.mul_sub, _root_.pow_succ']
  exact mul_dvd_mul_left X (h.trans (comp_sub_dvd p a b))

/-- `lem:improve`: `A ≡_m B` gives `XΦ(A) ≡_{m+1} XΦ(B)`. -/
theorem improve (Φ : ZPoly n) {m : ℕ} {A B : ZPoly n} (h : Γ ⊢[PRAAx] cong m A B) :
    Γ ⊢[PRAAx] cong (m + 1) (shiftX (comp Φ A)) (shiftX (comp Φ B)) := by
  apply cong_of_dvd
  rw [toP_shiftX, toP_shiftX, toP_comp, toP_comp]
  exact improve_dvd _ _ _ (dvd_of_cong h)

/-- The iterates `G^{(0)} = 0`, `G^{(k+1)} = XΦ(G^{(k)})`. -/
def iter (Φ : ZPoly n) : ℕ → ZPoly n
  | 0 => []
  | k + 1 => shiftX (comp Φ (iter Φ k))

/-- `G^{(k)} ≡_k G^{(k+1)}`. -/
theorem iter_step (Φ : ZPoly n) (k : ℕ) : Γ ⊢[PRAAx] cong k (iter Φ k) (iter Φ (k + 1)) := by
  induction k with
  | zero => exact conjFin_intro fun i => i.elim0
  | succ k ih => exact improve Φ ih

/-- `thm:fixed`, existence: `G^{(N+1)} ≡_{N+1} XΦ(G^{(N+1)})`. -/
theorem fixed (Φ : ZPoly n) (N : ℕ) :
    Γ ⊢[PRAAx] cong (N + 1) (iter Φ (N + 1)) (shiftX (comp Φ (iter Φ (N + 1)))) :=
  iter_step Φ (N + 1)

theorem unique_dvd {R : Type*} [CommRing R] (p g g' : R[X]) (N : ℕ)
    (hg : (X : R[X]) ^ (N + 1) ∣ g - X * p.comp g) (hg' : (X : R[X]) ^ (N + 1) ∣ g' - X * p.comp g') :
    ∀ m ≤ N + 1, (X : R[X]) ^ m ∣ g - g' := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 : (X : R[X]) ^ (m + 1) ∣ g - X * p.comp g := (pow_dvd_pow X hm).trans hg
    have h2 : (X : R[X]) ^ (m + 1) ∣ g' - X * p.comp g' := (pow_dvd_pow X hm).trans hg'
    have h3 := improve_dvd p g g' (ih (by omega))
    have e : g - g' = (g - X * p.comp g) - (g' - X * p.comp g') + (X * p.comp g - X * p.comp g') := by ring
    rw [e]
    exact dvd_add (dvd_sub h1 h2) h3

/-- `thm:fixed`, uniqueness: two solutions of `G ≡_{N+1} XΦ(G)` are congruent modulo `X^{N+1}`. -/
theorem unique (Φ : ZPoly n) (N : ℕ) {G G' : ZPoly n}
    (hG : Γ ⊢[PRAAx] cong (N + 1) G (shiftX (comp Φ G)))
    (hG' : Γ ⊢[PRAAx] cong (N + 1) G' (shiftX (comp Φ G'))) :
    Γ ⊢[PRAAx] cong (N + 1) G G' := by
  apply cong_of_dvd
  have d1 := dvd_of_cong hG
  have d2 := dvd_of_cong hG'
  rw [toP_shiftX, toP_comp] at d1 d2
  exact unique_dvd _ _ _ N d1 d2 (N + 1) le_rfl

end LeanProofs.IPRA.Algebra.TruncatedSeries
