import IPRADerivations.Analysis.Polynomials.PolynomialRemainder
import Mathlib.Algebra.BigOperators.Fin
import IPRADerivations.Core.Header

/-!
# Exact polynomial difference and Taylor identities

Packet: `foundations/ipra_coherent_methods_2026-11-15`, `paper/sections/04_lifting.tex`, Lemma
`lem:filtered-taylor` ("Finite polynomial difference and Taylor identities"): for `P ∈ B[X_1, …, X_m]^m` with
Jacobian `J`, if `h ∈ (F^k B)^m` then `P(x + h) − P(x) − J(x) h ∈ (F^{2k} B)^m` (T), and if
`x − a ∈ (F^1 B)^m` then every entry of `J(x) − J(a)` belongs to `F^1 B`. "Expand one monomial ... Every
remaining term has at least two factors among the `h_j`".

Both claims follow from exact identities with explicit polynomial witnesses, computed along a polynomial
expression `e : PE d` (`Analysis/PolynomialRemainder`, integer terms `ZT`):

* `pd e j`, the formal partial derivative (an expression), with `dv_eq`: `∇e(x)·v = ∑_j v_j ∂_j e(x)`;
* `tq e x v i j`, with `taylor_exact`: `e(x + v) − e(x) − ∇e(x)·v = ∑_{i,j} v_i v_j tq_{ij}` (in the ring of
  differences), and `taylor_eq` (the iPRA equation of integer terms): the remainder lies in the ideal generated
  by the products `v_i v_j`, so `v ∈ (F^k)^d` gives (T) for every filtration by ideals with `F^k F^k ⊆ F^{2k}`;
* `ls e x y i`, with `diff_exact`: `e(x) − e(y) = ∑_i (x_i − y_i) ls_i`; applied to `∂_j e` it gives the second
  claim (`x − a ∈ F^1` makes `J(x) − J(a)` an `F^1` combination);
* `taylor_power` (`F^k = q^k ℤ`, `cor:modular-hensel`): if `v_i = q^K w_i`, the remainder is
  `q^{2K} ∑ w_i w_j tq_{ij}`; this is the Taylor hypothesis assumed by `Foundations/FilteredLiftingStep`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FilteredTaylor

open_ipra
open LeanProofs.IPRA.Analysis.PolynomialRemainder

variable {k d : ℕ} {Γ : List (Fm PTm k)}

/-- The constant `p − q` as an integer term. -/
theorem toZ_const (p q : ℕ) : ZT.toZ Γ (⟨num p, num q⟩ : ZT k) = (p : Groth (Q Γ)) - q := by
  have h1 := ZT.toZ_natLit (Γ := Γ) (n := k) p
  have h2 := ZT.toZ_natLit (Γ := Γ) (n := k) q
  simp only [toZ_def, ZT.natLit, ZT.ofNat, Q.mk_zero, map_zero, sub_zero] at h1 h2 ⊢
  rw [h1, h2]

theorem toZ_zero : ZT.toZ Γ (ZT.ofNat (zero : PTm k)) = 0 := by
  simp only [ZT.toZ_ofNat, Q.mk_zero, map_zero]

/-- A fixed-length sum of integer terms. -/
def zsum : {d : ℕ} → (Fin d → ZT k) → ZT k
  | 0, _ => ZT.ofNat zero
  | _ + 1, f => f 0 + zsum (fun i => f i.succ)

theorem toZ_zsum : {d : ℕ} → (f : Fin d → ZT k) → ZT.toZ Γ (zsum f) = ∑ i, ZT.toZ Γ (f i)
  | 0, _ => by simp [zsum, toZ_zero]
  | _ + 1, f => by
    rw [zsum, ZT.toZ_add, toZ_zsum (fun i => f i.succ), Fin.sum_univ_succ]

/-- The formal partial derivative `∂_j e`. -/
def pd : PE d → Fin d → PE d
  | .const _ _, _ => .const 0 0
  | .var i, j => if i = j then .const 1 0 else .const 0 0
  | .add f g, j => .add (pd f j) (pd g j)
  | .mul f g, j => .add (.mul f (pd g j)) (.mul g (pd f j))

variable {x y v : Fin d → ZT k}

/-- `∇e(x)·v = ∑_j v_j ∂_j e(x)`. -/
theorem dv_eq (e : PE d) : ZT.toZ Γ (dv e x v) = ∑ j, ZT.toZ Γ (v j) * ZT.toZ Γ (ev (pd e j) x) := by
  induction e with
  | const p q => simp [dv, pd, ev, toZ_const, toZ_zero]
  | var i =>
    simp only [dv, pd]
    rw [Finset.sum_eq_single i]
    · simp [ev, toZ_const]
    · intro j _ hj; simp [Ne.symm hj, ev, toZ_const]
    · simp
  | add f g ihf ihg =>
    simp only [dv, pd, ev, ZT.toZ_add, ihf, ihg]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  | mul f g ihf ihg =>
    simp only [dv, pd, ev, ZT.toZ_add, ZT.toZ_mul, ihf, ihg, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic coefficients of the Taylor remainder. -/
def tq : PE d → (Fin d → ZT k) → (Fin d → ZT k) → Fin d → Fin d → ZT k
  | .const _ _, _, _, _, _ => ZT.ofNat zero
  | .var _, _, _, _, _ => ZT.ofNat zero
  | .add f g, x, v, i, j => tq f x v i j + tq g x v i j
  | .mul f g, x, v, i, j =>
    ev f x * tq g x v i j + ev (pd f i) x * ev (pd g j) x + dv f x v * tq g x v i j +
      tq f x v i j * ev g (fun l => x l + v l)

/-- (T), exactly: `e(x + v) − e(x) − ∇e(x)·v = ∑_{i,j} v_i v_j tq_{ij}`. -/
theorem taylor_exact (e : PE d) :
    ZT.toZ Γ (Analysis.PolynomialRemainder.rem e x v) = ∑ i, ∑ j, ZT.toZ Γ (v i) * ZT.toZ Γ (v j) * ZT.toZ Γ (tq e x v i j) := by
  induction e with
  | const p q => simp [Analysis.PolynomialRemainder.rem, ev, dv, tq, toZ_const, toZ_zero]
  | var i => simp [Analysis.PolynomialRemainder.rem, ev, dv, tq, toZ_zero]
  | add f g ihf ihg =>
    have hf := ihf; have hg := ihg
    simp only [Analysis.PolynomialRemainder.rem, ZT.toZ_sub] at hf hg
    have e1 : (∑ i, ∑ j, ZT.toZ Γ (v i) * ZT.toZ Γ (v j) * (ZT.toZ Γ (tq f x v i j) + ZT.toZ Γ (tq g x v i j))) =
        (∑ i, ∑ j, ZT.toZ Γ (v i) * ZT.toZ Γ (v j) * ZT.toZ Γ (tq f x v i j)) +
          ∑ i, ∑ j, ZT.toZ Γ (v i) * ZT.toZ Γ (v j) * ZT.toZ Γ (tq g x v i j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [Analysis.PolynomialRemainder.rem, ev, dv, tq, ZT.toZ_sub, ZT.toZ_add]
    rw [e1, ← hf, ← hg]; ring
  | mul f g ihf ihg =>
    have hf := ihf; have hg := ihg
    simp only [Analysis.PolynomialRemainder.rem, ZT.toZ_sub] at hf hg
    have key : ZT.toZ Γ (ev (.mul f g) (fun l => x l + v l)) - ZT.toZ Γ (ev (.mul f g) x) -
        ZT.toZ Γ (dv (.mul f g) x v) =
        ZT.toZ Γ (ev f x) * (ZT.toZ Γ (ev g (fun l => x l + v l)) - ZT.toZ Γ (ev g x) - ZT.toZ Γ (dv g x v)) +
        ZT.toZ Γ (dv f x v) * ZT.toZ Γ (dv g x v) +
        ZT.toZ Γ (dv f x v) * (ZT.toZ Γ (ev g (fun l => x l + v l)) - ZT.toZ Γ (ev g x) - ZT.toZ Γ (dv g x v)) +
        (ZT.toZ Γ (ev f (fun l => x l + v l)) - ZT.toZ Γ (ev f x) - ZT.toZ Γ (dv f x v)) *
          ZT.toZ Γ (ev g (fun l => x l + v l)) := by
      simp only [ev, dv, ZT.toZ_add, ZT.toZ_mul]; ring
    have hDD : ZT.toZ Γ (dv f x v) * ZT.toZ Γ (dv g x v) = ∑ i, ∑ j, ZT.toZ Γ (v i) * ZT.toZ Γ (v j) *
        (ZT.toZ Γ (ev (pd f i) x) * ZT.toZ Γ (ev (pd g j) x)) := by
      rw [dv_eq (Γ := Γ) (x := x) (v := v) f, dv_eq (Γ := Γ) (x := x) (v := v) g, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [Analysis.PolynomialRemainder.rem, ZT.toZ_sub]
    rw [key, hf, hg, hDD]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [tq, ZT.toZ_add, ZT.toZ_mul]
    ring

/-- The difference coefficients: `e(x) − e(y) = ∑_i (x_i − y_i) ls_i`. -/
def ls : PE d → (Fin d → ZT k) → (Fin d → ZT k) → Fin d → ZT k
  | .const _ _, _, _, _ => ZT.ofNat zero
  | .var i, _, _, j => if i = j then ⟨num 1, num 0⟩ else ZT.ofNat zero
  | .add f g, x, y, i => ls f x y i + ls g x y i
  | .mul f g, x, y, i => ev f x * ls g x y i + ev g y * ls f x y i

/-- The difference identity: `e(x) − e(y) = ∑_i (x_i − y_i) ls_i`. -/
theorem diff_exact (e : PE d) :
    ZT.toZ Γ (ev e x - ev e y) = ∑ i, (ZT.toZ Γ (x i) - ZT.toZ Γ (y i)) * ZT.toZ Γ (ls e x y i) := by
  induction e with
  | const p q => simp [ev, ls, toZ_const, toZ_zero]
  | var i =>
    simp only [ev, ls, ZT.toZ_sub]
    rw [Finset.sum_eq_single i]
    · simp [toZ_const]
    · intro j _ hj; simp [Ne.symm hj, toZ_zero]
    · simp
  | add f g ihf ihg =>
    simp only [ZT.toZ_sub] at ihf ihg
    have e1 : (∑ i, (ZT.toZ Γ (x i) - ZT.toZ Γ (y i)) * (ZT.toZ Γ (ls f x y i) + ZT.toZ Γ (ls g x y i))) =
        (∑ i, (ZT.toZ Γ (x i) - ZT.toZ Γ (y i)) * ZT.toZ Γ (ls f x y i)) +
          ∑ i, (ZT.toZ Γ (x i) - ZT.toZ Γ (y i)) * ZT.toZ Γ (ls g x y i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [ev, ls, ZT.toZ_sub, ZT.toZ_add]
    rw [e1, ← ihf, ← ihg]; ring
  | mul f g ihf ihg =>
    simp only [ZT.toZ_sub] at ihf ihg
    have key : ZT.toZ Γ (ev (.mul f g) x) - ZT.toZ Γ (ev (.mul f g) y) =
        ZT.toZ Γ (ev f x) * (ZT.toZ Γ (ev g x) - ZT.toZ Γ (ev g y)) +
        ZT.toZ Γ (ev g y) * (ZT.toZ Γ (ev f x) - ZT.toZ Γ (ev f y)) := by
      simp only [ev, ZT.toZ_mul]; ring
    simp only [ZT.toZ_sub]
    rw [key, ihf, ihg]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ls, ZT.toZ_add, ZT.toZ_mul]
    ring

/-- (T) as an iPRA equation of integer terms. -/
theorem taylor_eq (e : PE d) :
    Γ ⊢[PRAAx] ZT.eq (Analysis.PolynomialRemainder.rem e x v) (zsum fun i => zsum fun j => v i * v j * tq e x v i j) := by
  refine ZT.derive ?_
  rw [taylor_exact]
  simp only [toZ_zsum, ZT.toZ_mul]

/-- The difference identity as an iPRA equation; at `pd e j` it is the second claim of the lemma. -/
theorem diff_eq (e : PE d) :
    Γ ⊢[PRAAx] ZT.eq (ev e x - ev e y) (zsum fun i => (x i - y i) * ls e x y i) := by
  refine ZT.derive ?_
  rw [diff_exact]
  simp only [toZ_zsum, ZT.toZ_mul, ZT.toZ_sub]

/-- `F^K = q^K ℤ`: if `v_i = q^K w_i`, the remainder is `q^{2K} ∑ w_i w_j tq_{ij}`. -/
theorem taylor_power {q K : PTm k} {w : Fin d → ZT k} (e : PE d)
    (hv : ∀ i, Γ ⊢[PRAAx] ZT.eq (v i) (ZT.ofNat (pw q K) * w i)) :
    Γ ⊢[PRAAx] ZT.eq (Analysis.PolynomialRemainder.rem e x v)
      (ZT.ofNat (pw q K * pw q K) * zsum fun i => zsum fun j => w i * w j * tq e x v i j) := by
  refine ZT.derive ?_
  have hv' : ∀ i, ZT.toZ Γ (v i) = Groth.ι (Q.mk Γ (pw q K)) * ZT.toZ Γ (w i) := fun i => by
    have h := ZT.toZ_eq (hv i)
    simpa only [ZT.toZ_mul, ZT.toZ_ofNat] using h
  rw [taylor_exact]
  simp only [toZ_zsum, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul, hv', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end LeanProofs.IPRA.Foundations.FilteredTaylor
