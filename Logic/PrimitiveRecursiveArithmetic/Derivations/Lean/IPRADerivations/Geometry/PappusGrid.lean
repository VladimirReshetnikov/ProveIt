import IPRADerivations.Probability.Lotus

/-!
# Pappus's theorems for finite grids and polygonal chains (`pappus_centroid_ipra_2026-11-15`, `thm:grid-pappus`, `thm:polygon-pappus`)

Packet: `geometry/pappus_centroid_ipra_2026-11-15`.

`thm:grid-pappus`: "Let `G = (C_0, …, C_{t−1})` be a finite list of grid cells ... Define
`A(G) = ∑_{i<t} A(C_i)`, `M(G) = ∑_{i<t} M(C_i)`, `V(G) = ∑_{i<t} V(C_i)`. For every finite grid
lamina `G`, `V(G) = τ M(G)`. If `A(G) > 0` and `r̄(G) = M(G)/A(G)`, then `V(G) = τ A(G) r̄(G)`."
Proof: "Sum `prop:cell-pappus`."

`thm:polygon-pappus`: "For every finite polygonal chain `P` in `r ≥ 0`, `S(P) = τ M(P)`. If
`L(P) > 0` and `r̄(P) = M(P)/L(P)`, then `S(P) = τ L(P) r̄(P)`." Proof: "Sum
`prop:segment-pappus` over the finitely many segments and distribute multiplication by `τ` over
the finite sum."

`Geometry/PappusCell` has one cell and two cells. Here the number of cells is a term `t`, the
cells are a term-defined family with corners `a(i) ≤ b(i)`, `c(i)`, `d(i)` in natural grid
units, and `T` is a parameter standing for the turn constant in the chosen unit. Doubled
quantities clear the factor `1/2`:

* `cell_nat`: `(b² ∸ a²) e = (a + b)((b ∸ a) e)` for `a ≤ b` (`prop:cell-pappus` with corners);
* `areaB`, `momB`, `volB`: the bodies `A(C_i)`, `2 M(C_i)` and `2 V(C_i)/τ`;
* `grid_pappus`: `∑_{i<t} T · volB(i) = T · ∑_{i<t} momB(i)`, that is `2 V(G) = τ · 2 M(G)`;
* `centroid_form`: from `2 V = T · 2 M` and `2 M · q = 2 (A · p)` (the centroid radius is
  `p/q`), `2 V · q = T · 2 (A · p)`: the cleared form of `V = τ A r̄`;
* `grid_centroid`: `centroid_form` for the grid sums;
* `pappus_sum`: for arbitrary bodies, `S(j) = T · M(j)` for all `j < N` gives
  `∑ S = T · ∑ M`;
* `segB`, `polygon_pappus`, `polygon_centroid`: the chain with vertex radii `r(j)` and segment
  lengths `ℓ(j)`, doubled segment moment `(r(j) + r(j+1)) ℓ(j)`.

Not derived here: that the sums are the geometric volume and area (disjointness of the rotated
cells, zero content of faces), the segment surface identity itself (`prop:segment-pappus` is a
limit, the frustum squeeze), and the limits `thm:surface-main`, `thm:volume-main`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PappusGrid

open_ipra
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## One cell with natural corners -/

/-- `prop:cell-pappus` with corners: `(b² ∸ a²) e = (a + b)((b ∸ a) e)` for `a ≤ b`. -/
theorem cell_nat {a b : PTm k} (e : PTm k) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] monus (b * b) (a * a) * e ≐ (a + b) * (monus b a * e) := by
  have hb := eq_add_of_le h
  have hsq : Γ ⊢[PRAAx] b * b ≐
      a * a + (a * monus b a + a * monus b a + monus b a * monus b a) := by
    have e₁ := natEq hb
    apply deriveNat; ipra_simps
    linear_combination (𝔞 b + 𝔞 a + 𝔞 (monus b a)) * e₁
  have hm : Γ ⊢[PRAAx] monus (b * b) (a * a) ≐
      a * monus b a + a * monus b a + monus b a * monus b a :=
    (congrMonus hsq (.eqRefl _)).eqTrans (add_monus' _ _)
  have e₁ := natEq hb
  have e₂ := natEq hm
  apply deriveNat; ipra_simps
  linear_combination 𝔞 e * e₂ - 𝔞 e * 𝔞 (monus b a) * e₁

/-! ## The centroid form -/

/-- From `V = T · M` and `M · q = A · p + A · p`: `V · q = T · (A · p + A · p)`. -/
theorem centroid_form {V M A T p q : PTm k} (hv : Γ ⊢[PRAAx] V ≐ T * M)
    (hc : Γ ⊢[PRAAx] M * q ≐ A * p + A * p) : Γ ⊢[PRAAx] V * q ≐ T * (A * p + A * p) := by
  ipra_lc 𝔞 q * natEq hv + 𝔞 T * natEq hc

/-! ## A pointwise proportionality, summed -/

private theorem shift_pair (a b : PTm k) :
    Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

/-- `S(j) = T · M(j)` for all `j < N` gives `∑_{j<N} S(j) = T · ∑_{j<N} M(j)`. -/
theorem pappus_sum (S M : PTm 2) {N T x : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 S (var 0) (Syn.shift x) ≐ Syn.shift T * inst2 M (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF S) N x ≐ T * ap2 (sumF M) N x := by
  refine (sum_congr_bounded S (cmB M) x (pairT T x) N ?_).eqTrans (sum_const_mul M N T x)
  refine .allI (.impI ?_)
  rw [shift_pair, inst2_cmB]
  exact (Prf.impE h.allOpen.wk Prf.hyp0).eqTrans
    (congrMul (fst_pair _ _) (congrInst2 M (.eqRefl _) (snd_pair _ _))).eqSymm

/-! ## Grid laminae -/

section Grid

variable (a b c d : PTm 2)

/-- The area `A(C_i) = (b ∸ a)(d ∸ c)` of cell `i`. -/
def areaB : PTm 2 := monus b a * monus d c

/-- The doubled first moment `2 M(C_i) = (a + b)(b ∸ a)(d ∸ c)`. -/
def momB : PTm 2 := (a + b) * (monus b a * monus d c)

/-- The doubled volume of the rotated cell divided by the turn constant:
`(b² ∸ a²)(d ∸ c)`. -/
def volB : PTm 2 := monus (b * b) (a * a) * monus d c

theorem inst2_areaB (i x : PTm k) : inst2 (areaB a b c d) i x =
    monus (inst2 b i x) (inst2 a i x) * monus (inst2 d i x) (inst2 c i x) := by
  simp [inst2, areaB]

theorem inst2_momB (i x : PTm k) : inst2 (momB a b c d) i x =
    (inst2 a i x + inst2 b i x) *
      (monus (inst2 b i x) (inst2 a i x) * monus (inst2 d i x) (inst2 c i x)) := by
  simp [inst2, momB]

theorem inst2_volB (i x : PTm k) : inst2 (volB a b c d) i x =
    monus (inst2 b i x * inst2 b i x) (inst2 a i x * inst2 a i x) *
      monus (inst2 d i x) (inst2 c i x) := by
  simp [inst2, volB]

/-- The cells of the grid agree pointwise: `volB(i) = momB(i)` when `a(i) ≤ b(i)`. -/
theorem cell_pointwise {i x : PTm k} (h : Γ ⊢[PRAAx] le (inst2 a i x) (inst2 b i x)) :
    Γ ⊢[PRAAx] inst2 (volB a b c d) i x ≐ inst2 (momB a b c d) i x := by
  rw [inst2_volB, inst2_momB]
  exact cell_nat _ h

/-- `thm:grid-pappus`: `2 V(G) = τ · 2 M(G)` for a grid of `t` cells. -/
theorem grid_pappus {t T x : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift t) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 b (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF (cmB (volB a b c d))) t (pairT T x) ≐
      T * ap2 (sumF (momB a b c d)) t x :=
  (sum_const_mul (volB a b c d) t T x).eqTrans (congrMul (.eqRefl _)
    (sum_congr_bounded (volB a b c d) (momB a b c d) x x t
      (.allI (.impI (cell_pointwise a b c d (.impE h.allOpen.wk Prf.hyp0))))))

/-- `thm:grid-pappus`, centroid form: if the centroid radius is `p/q`, that is
`2 M(G) · q = 2 (A(G) · p)`, then `2 V(G) · q = τ · 2 (A(G) · p)`. -/
theorem grid_centroid {t T x p q : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift t) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 b (var 0) (Syn.shift x))))
    (hc : Γ ⊢[PRAAx] ap2 (sumF (momB a b c d)) t x * q ≐
      ap2 (sumF (areaB a b c d)) t x * p + ap2 (sumF (areaB a b c d)) t x * p) :
    Γ ⊢[PRAAx] ap2 (sumF (cmB (volB a b c d))) t (pairT T x) * q ≐
      T * (ap2 (sumF (areaB a b c d)) t x * p + ap2 (sumF (areaB a b c d)) t x * p) :=
  centroid_form (grid_pappus a b c d h) hc

end Grid

/-! ## Polygonal chains -/

section Polygon

variable (r l : PTm 2)

/-- The doubled moment `(r(j) + r(j+1)) ℓ(j)` of segment `j`. -/
def segB : PTm 2 := (r + Syn.subst ![succ (var 0), var 1] r) * l

theorem inst2_segB (j x : PTm k) : inst2 (segB r l) j x =
    (inst2 r j x + inst2 r (succ j) x) * inst2 l j x := by
  simp only [inst2, segB, PTm.subst_mul, PTm.subst_add, Syn.subst_subst]
  congr 2
  congr 1; funext i; fin_cases i <;> simp

/-- `thm:polygon-pappus`: if every segment has doubled surface `S(j) = τ · (r(j) + r(j+1)) ℓ(j)`
(`prop:segment-pappus`), then `2 S(P) = τ · 2 M(P)`. -/
theorem polygon_pappus (S : PTm 2) {s T x : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift s) ⟶
      (inst2 S (var 0) (Syn.shift x) ≐ Syn.shift T * inst2 (segB r l) (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF S) s x ≐ T * ap2 (sumF (segB r l)) s x :=
  pappus_sum S (segB r l) h

/-- `thm:polygon-pappus`, centroid form: if `2 M(P) · q = 2 (L(P) · p)`, then
`2 S(P) · q = τ · 2 (L(P) · p)`. -/
theorem polygon_centroid (S : PTm 2) {s T x p q : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift s) ⟶
      (inst2 S (var 0) (Syn.shift x) ≐ Syn.shift T * inst2 (segB r l) (var 0) (Syn.shift x))))
    (hc : Γ ⊢[PRAAx] ap2 (sumF (segB r l)) s x * q ≐
      ap2 (sumF l) s x * p + ap2 (sumF l) s x * p) :
    Γ ⊢[PRAAx] ap2 (sumF S) s x * q ≐ T * (ap2 (sumF l) s x * p + ap2 (sumF l) s x * p) :=
  centroid_form (polygon_pappus r l S h) hc

end Polygon

end LeanProofs.IPRA.Geometry.PappusGrid
