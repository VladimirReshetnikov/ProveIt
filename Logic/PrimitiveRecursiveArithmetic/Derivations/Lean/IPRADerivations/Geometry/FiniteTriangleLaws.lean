import IPRADerivations.Core.PolynomialInequalities
import IPRADerivations.Core.LinearCombination

/-!
# The finite radical Heron and finite trigonometric laws (`triangle_formulas_ipra`, `thm:finite-heron`, `thm:finite-trig`)

Packet: `geometry/triangle_formulas_ipra`, Section 8. The squared sides `W, V, U` of a rational
triangle are replaced by squares `a_n², b_n², c_n²` of lower mesh roots, with deficits
"`0 ≤ W − a_n², V − b_n², U − c_n² ≤ (2Q + 1)ε ≤ 3Qε`" (8.2), all squared sides in `[0, Q²]`.

`thm:finite-trig`: "Let `e_a = W − a_n²`, `e_b = V − b_n²`, `e_c = U − c_n²` ... Since
`W − U − V + 2p = 0`, `a_n² − b_n² − c_n² + 2 b_n c_n C_A = −e_a + e_b + e_c`", and for the
radius "the exact center identity gives `4h²Q_R = UVW`. The three squared lower roots lie below
their targets, and a telescoping product difference gives `0 ≤ UVW − a_n²b_n²c_n² ≤ 9Q⁵ε`".

`thm:finite-heron`: "Every squared side lies in `[0, Q²]` and changes by at most `3Qε`. A
product of two such variables changes by at most `6Q³ε`, as does its square. There are three
product terms of coefficient `2` and three negative square terms. Therefore
`|P_n − Δ²| ≤ (54/16) Q³ε`" (8.3); then "Clipping at zero cannot increase the distance to
`Δ² ≥ 0`. Put `q = max(P_n, 0)`; then `|q − Δ²| ≤ η²`. ... If `H_k ≥ Δ`, then
`H_k² ≤ q ≤ Δ² + η²`, giving `H_k − Δ ≤ η` by square comparison. If `Δ ≥ H_k`, then
`Δ² ≤ q + η² < (H_k + η)² + η² ≤ (H_k + 2η)²`, giving `Δ − H_k ≤ 2η`."

With `A₂, B₂, C₂` for the squared roots, `E` for the deficit bound and `Q₂` for `Q²`:

* `cos_defect_upper`, `cos_defect_lower`: `−E ≤ A₂ − B₂ − C₂ + 2p ≤ 2E` (within the packet's
  `3E = 9Qε`);
* `product_defect_lower`, `product_defect_upper`: `A₂B₂C₂ ≤ 4h²Q_R` and
  `4h²Q_R − A₂B₂C₂ ≤ 3 E Q₂²` (with `E = 3Qε` this is `9Q⁵ε`);
* `heron_defect_upper`, `heron_defect_lower`: for `F(x, y, z) = 2(xy + yz + zx) − x² − y² − z²`,
  `−6 Q₂ E ≤ F(W, V, U) − F(A₂, B₂, C₂) ≤ 12 Q₂ E` (within the packet's `18 Q₂ E = 54Q³ε`);
  `F(W, V, U) = 4t²` and `F(A₂, B₂, C₂) = 16 P_n`.

These are closed implications between integer polynomial relations
(`Core/PolynomialInequalities`). Over the natural numbers (a common denominator cleared):

* `sq_mono`, `square_lt`, `square_compare`: `w ≤ u ⟹ w² ≤ u²`; `u² < w² ⟹ u < w`;
  `u² ≤ v² + e² ⟹ u ≤ v + e` (the square comparison);
* `clip_upper`, `clip_lower`: clipping an integer `P = p⁺ − p⁻` at zero keeps both bounds
  `P ≤ b` and `b ≤ P + e` for natural `b`;
* `heron_upper`, `heron_lower`, `finite_heron`: from the mesh bracket `H² ≤ q < (H + η)²` for
  the clipped radicand `q` and `|P − D²| ≤ η²`: `H ≤ D + η` and `D < H + 2η`, that is
  `|H_k − Δ| ≤ 2η = 2^{-k}` (8.1).

Not derived: the mesh deficit (8.2) for the three sides from `Geometry/MeshBracket`, the
precision arithmetic (`4Q³ε ≤ 2^{-2k-2}`, `Q ≤ 2^Q`), and the final radius comparison
`|K_n − 2R_k| ≤ 2^{-k}`.
-/

namespace LeanProofs.IPRA.Geometry.FiniteTriangleLaws

open LeanProofs.ConciseIPRA LeanProofs.IPRA

/-! ## The cosine defect: `U, V, W, p, A₂, B₂, C₂, E` -/

section Cosine

open ZExp

local notation "U" => (ZExp.var 0 : ZExp 8)
local notation "V" => (ZExp.var 1 : ZExp 8)
local notation "W" => (ZExp.var 2 : ZExp 8)
local notation "pp" => (ZExp.var 3 : ZExp 8)
local notation "A₂" => (ZExp.var 4 : ZExp 8)
local notation "B₂" => (ZExp.var 5 : ZExp 8)
local notation "C₂" => (ZExp.var 6 : ZExp 8)
local notation "E" => (ZExp.var 7 : ZExp 8)

/-- The law of cosines `W = U + V − 2p` and the three deficits in `[0, E]`. -/
abbrev hypsC : List (Rel 8) :=
  [.eq W (U + V - 2 * pp),
   .le 0 (W - A₂), .le (W - A₂) E,
   .le 0 (V - B₂), .le (V - B₂) E,
   .le 0 (U - C₂), .le (U - C₂) E]

/-- `thm:finite-trig`: `a_n² − b_n² − c_n² + 2p ≤ 2E`. -/
theorem cos_defect_upper :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (impR hypsC (.le (A₂ - B₂ - C₂ + 2 * pp) (2 * E))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨hW, a0, a1, b0, b1, c0, c1⟩ := h
    exact C.of_eq (C.add (C.add a0 b1) c1) (by linear_combination (-1) * hW))

/-- `thm:finite-trig`: `−E ≤ a_n² − b_n² − c_n² + 2p`. -/
theorem cos_defect_lower :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (impR hypsC (.le (-E) (A₂ - B₂ - C₂ + 2 * pp))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨hW, a0, a1, b0, b1, c0, c1⟩ := h
    exact C.of_eq (C.add (C.add a1 b0) c0) (by linear_combination hW))

end Cosine

/-! ## The product defect: `U, V, W, A₂, B₂, C₂, E, Q₂, h², Q_R` -/

section Product

open ZExp

local notation "U" => (ZExp.var 0 : ZExp 10)
local notation "V" => (ZExp.var 1 : ZExp 10)
local notation "W" => (ZExp.var 2 : ZExp 10)
local notation "A₂" => (ZExp.var 3 : ZExp 10)
local notation "B₂" => (ZExp.var 4 : ZExp 10)
local notation "C₂" => (ZExp.var 5 : ZExp 10)
local notation "E" => (ZExp.var 6 : ZExp 10)
local notation "Q₂" => (ZExp.var 7 : ZExp 10)
local notation "H₂" => (ZExp.var 8 : ZExp 10)
local notation "QR" => (ZExp.var 9 : ZExp 10)

/-- Squared roots below their targets with deficits at most `E`, targets at most `Q₂`, and the
centre identity `4h²Q_R = UVW`. -/
abbrev hypsP : List (Rel 10) :=
  [.le 0 A₂, .le 0 B₂, .le 0 C₂,
   .le A₂ W, .le (W - A₂) E,
   .le B₂ V, .le (V - B₂) E,
   .le C₂ U, .le (U - C₂) E,
   .le U Q₂, .le V Q₂, .le W Q₂,
   .eq (4 * H₂ * QR) (U * V * W)]

/-- (8.6), lower half: `a_n² b_n² c_n² ≤ 4h²Q_R`. -/
theorem product_defect_lower :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (impR hypsP (.le (A₂ * B₂ * C₂) (4 * H₂ * QR))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨a0, b0, c0, ea, Ea, eb, Eb, ec, Ec, uq, vq, wq, hc⟩ := h
    have hV := C.add eb b0
    have hU := C.add ec c0
    exact C.of_eq
      (C.add (C.add (C.mul (C.mul ea hV) hU) (C.mul (C.mul a0 eb) hU)) (C.mul (C.mul a0 b0) ec))
      (by linear_combination hc))

/-- (8.6), upper half: `4h²Q_R − a_n² b_n² c_n² ≤ 3 E Q₂²`. -/
theorem product_defect_upper :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 10)
      (impR hypsP (.le (4 * H₂ * QR - A₂ * B₂ * C₂) (3 * E * Q₂ ^ 2))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨a0, b0, c0, ea, Ea, eb, Eb, ec, Ec, uq, vq, wq, hc⟩ := h
    have hV := C.add eb b0
    have hU := C.add ec c0
    have hQ := C.add uq hU
    have hQA := C.add wq ea
    have hQB := C.add vq eb
    exact C.of_eq
      (C.add (C.add
        (C.add (C.mul Ea (C.mul hQ hQ)) (C.mul ea (C.add (C.mul hQ vq) (C.mul hV uq))))
        (C.add (C.mul Eb (C.mul hQ hQ)) (C.mul eb (C.add (C.mul hQ hQA) (C.mul a0 uq)))))
        (C.add (C.mul Ec (C.mul hQ hQ)) (C.mul ec (C.add (C.mul hQ hQA) (C.mul a0 hQB)))))
      (by linear_combination (-1) * hc))

end Product

/-! ## The Heron defect: `U, V, W, A₂, B₂, C₂, E, Q₂` -/

section Heron

open ZExp

local notation "U" => (ZExp.var 0 : ZExp 8)
local notation "V" => (ZExp.var 1 : ZExp 8)
local notation "W" => (ZExp.var 2 : ZExp 8)
local notation "A₂" => (ZExp.var 3 : ZExp 8)
local notation "B₂" => (ZExp.var 4 : ZExp 8)
local notation "C₂" => (ZExp.var 5 : ZExp 8)
local notation "E" => (ZExp.var 6 : ZExp 8)
local notation "Q₂" => (ZExp.var 7 : ZExp 8)

/-- `F(x, y, z) = 2(xy + yz + zx) − x² − y² − z²`: `16 s(s − a)(s − b)(s − c)` in the squared
sides. -/
abbrev Fh (x y z : ZExp 8) : ZExp 8 := 2 * (x * y + y * z + z * x) - x ^ 2 - y ^ 2 - z ^ 2

abbrev hypsH : List (Rel 8) :=
  [.le 0 A₂, .le 0 B₂, .le 0 C₂,
   .le A₂ W, .le (W - A₂) E,
   .le B₂ V, .le (V - B₂) E,
   .le C₂ U, .le (U - C₂) E,
   .le U Q₂, .le V Q₂, .le W Q₂]

/-- (8.3), upper half: `F(W, V, U) − F(A₂, B₂, C₂) ≤ 12 Q₂ E`. -/
theorem heron_defect_upper :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (impR hypsH (.le (Fh W V U - Fh A₂ B₂ C₂) (12 * Q₂ * E))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨a0, b0, c0, ea, Ea, eb, Eb, ec, Ec, uq, vq, wq⟩ := h
    have hW := C.add ea a0
    have hU := C.add ec c0
    have hQ := C.add uq hU
    have hQA := C.add wq ea
    have hQB := C.add vq eb
    have hQC := C.add uq ec
    have qWV := C.add (C.add (C.mul Ea hQ) (C.mul ea vq)) (C.add (C.mul Eb hQ) (C.mul eb hQA))
    have qVU := C.add (C.add (C.mul Eb hQ) (C.mul eb uq)) (C.add (C.mul Ec hQ) (C.mul ec hQB))
    have qUW := C.add (C.add (C.mul Ec hQ) (C.mul ec wq)) (C.add (C.mul Ea hQ) (C.mul ea hQC))
    have sW := C.add (C.mul ea hW) (C.mul a0 ea)
    have sV := C.add (C.mul eb (C.add eb b0)) (C.mul b0 eb)
    have sU := C.add (C.mul ec hU) (C.mul c0 ec)
    exact C.of_eq
      (C.add (C.mul (C.ofNat 2) (C.add (C.add qWV qVU) qUW)) (C.add (C.add sW sV) sU))
      (by ring))

/-- (8.3), lower half: `−6 Q₂ E ≤ F(W, V, U) − F(A₂, B₂, C₂)`. -/
theorem heron_defect_lower :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (impR hypsH (.le (-(6 * Q₂ * E)) (Fh W V U - Fh A₂ B₂ C₂))) :=
  derive_rel _ _ (by
    ipra_cone R C ρ h
    obtain ⟨a0, b0, c0, ea, Ea, eb, Eb, ec, Ec, uq, vq, wq⟩ := h
    have hW := C.add ea a0
    have hV := C.add eb b0
    have hU := C.add ec c0
    have hQ := C.add uq hU
    have hQA := C.add wq ea
    have hQB := C.add vq eb
    have hQC := C.add uq ec
    have pWV := C.add (C.mul ea hV) (C.mul a0 eb)
    have pVU := C.add (C.mul eb hU) (C.mul b0 ec)
    have pUW := C.add (C.mul ec hW) (C.mul c0 ea)
    have rW := C.add (C.add (C.mul Ea hQ) (C.mul ea wq)) (C.add (C.mul Ea hQ) (C.mul ea hQA))
    have rV := C.add (C.add (C.mul Eb hQ) (C.mul eb vq)) (C.add (C.mul Eb hQ) (C.mul eb hQB))
    have rU := C.add (C.add (C.mul Ec hQ) (C.mul ec uq)) (C.add (C.mul Ec hQ) (C.mul ec hQC))
    exact C.of_eq
      (C.add (C.mul (C.ofNat 2) (C.add (C.add pWV pVU) pUW)) (C.add (C.add rW rV) rU))
      (by ring))

end Heron

/-! ## Square comparison over the natural numbers -/

section Order

open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `w ≤ u ⟹ w² ≤ u²`. -/
theorem sq_mono {u w : PTm n} (h : Γ ⊢[PRAAx] le w u) : Γ ⊢[PRAAx] le (w * w) (u * u) := by
  refine le_of_eq_add (d := w * monus u w + w * monus u w + monus u w * monus u w) ?_
  ipra_lc (𝔞 u + 𝔞 w + 𝔞 (monus u w)) * natEq (eq_add_of_le h)

/-- `u² < w² ⟹ u < w`. -/
theorem square_lt {u w : PTm n} (h : Γ ⊢[PRAAx] lt (u * u) (w * w)) : Γ ⊢[PRAAx] lt u w :=
  .orE (lt_or_le u w) Prf.hyp0 (not_succ_le_self _ _ (le_trans h.wk (sq_mono Prf.hyp0)))

private theorem sq_gap {u v e d : PTm n} (hu : Γ ⊢[PRAAx] u ≐ succ (v + e) + d) :
    Γ ⊢[PRAAx] u * u ≐ succ (v * v + e * e +
      (v * e + v * e + ((v + e) * succ d + (v + e) * succ d) + (d * d + (d + d)))) := by
  ipra_lc (𝔞 u + 𝔞 v + 𝔞 e + 1 + 𝔞 d) * natEq hu

/-- The square comparison: `u² ≤ v² + e² ⟹ u ≤ v + e`. -/
theorem square_compare {u v e : PTm n} (h : Γ ⊢[PRAAx] le (u * u) (v * v + e * e)) :
    Γ ⊢[PRAAx] le u (v + e) := by
  refine .orE (lt_or_le (v + e) u) ?_ Prf.hyp0
  have hsq := sq_gap (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := lt (v + e) u)))
  exact not_succ_le_self _ _ (le_trans (le_congr hsq (.eqRefl _) h.wk) (le_add_right _ _))

/-! ## Clipping at zero -/

/-- `a ≤ b + c ⟹ a ∸ c ≤ b`: clipping `P = a − c` at zero keeps the upper bound `P ≤ b`. -/
theorem clip_upper {a b c : PTm n} (h : Γ ⊢[PRAAx] le a (b + c)) :
    Γ ⊢[PRAAx] le (monus a c) b := by
  refine .orE (le_total c a) ?_ ?_
  · refine le_of_eq_add (d := monus (b + c) a) ?_
    ipra_lc natEq (eq_add_of_le (h.wk (ψ := le c a))) + natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le c a)))
  · exact le_congr (Prf.eqSymm Prf.hyp0) (.eqRefl b) (zero_le b)

/-- `b + c ≤ a + e ⟹ b ≤ (a ∸ c) + e`: clipping `P = a − c` at zero keeps the bound
`b ≤ P + e` for natural `b`. -/
theorem clip_lower {a b c e : PTm n} (h : Γ ⊢[PRAAx] le (b + c) (a + e)) :
    Γ ⊢[PRAAx] le b (monus a c + e) := by
  refine .orE (le_total c a) ?_ ?_
  · refine le_of_eq_add (d := monus (a + e) (b + c)) ?_
    have e₁ := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le c a)))
    have e₂ := natEq (eq_add_of_le (h.wk (ψ := le c a)))
    apply deriveNat; ipra_simps
    linear_combination e₂ - e₁
  · refine le_of_eq_add (d := monus c a + monus (a + e) (b + c)) ?_
    have z := natEq (Prf.hyp0 (Γ := Γ) (φ := le a c))
    have e₁ := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le a c)))
    have e₂ := natEq (eq_add_of_le (h.wk (ψ := le a c)))
    apply deriveNat; ipra_simps
    linear_combination z + e₂ + e₁

/-! ## The end of the finite Heron argument -/

/-- `H² ≤ q ≤ D² + η²` gives `H ≤ D + η`. -/
theorem heron_upper {H D q η : PTm n} (h₁ : Γ ⊢[PRAAx] le (H * H) q)
    (h₃ : Γ ⊢[PRAAx] le q (D * D + η * η)) : Γ ⊢[PRAAx] le H (D + η) :=
  square_compare (le_trans h₁ h₃)

/-- `D² ≤ q + η²` and `q < (H + η)²` give `D < H + 2η`. -/
theorem heron_lower {H D q η : PTm n} (h₂ : Γ ⊢[PRAAx] lt q ((H + η) * (H + η)))
    (h₄ : Γ ⊢[PRAAx] le (D * D) (q + η * η)) : Γ ⊢[PRAAx] lt D (H + (η + η)) := by
  refine square_lt (le_of_eq_add (d := monus (q + η * η) (D * D) +
    monus ((H + η) * (H + η)) (succ q) + (H * η + H * η + (η * η + η * η))) ?_)
  ipra_lc natEq (eq_add_of_le h₄) + natEq (eq_add_of_le h₂)

/-- `thm:finite-heron`, the last step: for an integer radicand `P = p⁺ − p⁻` with
`|P − D²| ≤ η²`, clipped to `q = p⁺ ∸ p⁻`, and the mesh bracket `H² ≤ q < (H + η)²`:
`H ≤ D + η` and `D < H + 2η`. -/
theorem finite_heron {H D η p₁ p₂ : PTm n}
    (hup : Γ ⊢[PRAAx] le p₁ (D * D + η * η + p₂))
    (hlo : Γ ⊢[PRAAx] le (D * D + p₂) (p₁ + η * η))
    (h₁ : Γ ⊢[PRAAx] le (H * H) (monus p₁ p₂))
    (h₂ : Γ ⊢[PRAAx] lt (monus p₁ p₂) ((H + η) * (H + η))) :
    Γ ⊢[PRAAx] le H (D + η) ⋏ lt D (H + (η + η)) :=
  .andI (heron_upper h₁ (clip_upper hup)) (heron_lower h₂ (clip_lower hlo))

end Order

end LeanProofs.IPRA.Geometry.FiniteTriangleLaws
