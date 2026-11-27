import Lib.Weil.DualPair.KernelLaws
import Lib.Weil.Lift

/-!
# Theta lifts for families of characters over a real edge and the seesaw of periods

This file constructs theta lifts between two unitary groups for a whole family of characters at
once. For hermitian spaces `S`, `T` and characters `a`, `b` of the norm-one adeles,
`New.pairWeil S T a b` is the Weil representation of the pair. `New.modDatum` is a datum given by a
Fock vector at infinity and a function modulo `𝔪`, and a "type" is a kernel on the real points that
cuts out a space of forms.

## Main definitions and results

* `New.Exchange.modLift`, `New.Exchange.modTransposedLift`: the lift of forms from `S` to `T` and
  the transposed lift back.
* `New.Exchange.IsConjKernelPair`, `New.Exchange.IsEdgeFamily`: a pair of conjugate cuspidal types;
  a family of characters with common weights for which two such pairs and a polynomial form a real
  edge (`New.IsEdge`). `New.Exchange.isEdgeFamily_of_paramsCorrespond` produces edges from
  corresponding parameters.
* `New.Exchange.pairLift`, `New.Exchange.pairTransposedLift`, `New.Exchange.IsPairEdge`: lift,
  transposed lift and edge when the two characters of the pair are given separately. `IsPairEdge`
  has one type on each group and lets the two characters have different tame parts.
* `New.Exchange.IsEdgeFamily.exists_lift_eq_realConv`,
  `New.Exchange.IsEdgeFamily.petersson_lift_eq_mul_inner_modTransposedLift`: replacing the
  polynomial of the edge by another one changes the lift by right convolution with a continuous
  compactly supported function on the real points; the Petersson product of a form with this lift is
  a constant times that of its transposed lift. The function and the constant do not depend on the
  finite data.
* `New.Space.periodPairing`: the bilinear period `∫ M z * f z * y (j z * r)` of a form `f` on `S`
  and a form `y` on `T`, for a moderate weight with function `M` and map `j` and a real point `r`.
* `New.Exchange.seesaw_periods`: suppose the theta kernels of two pairs agree up to moderate weights
  on a spanning set of polynomials (`New.Exchange.IsSeesawMatched`). Then proportionality to a fixed
  vector passes from the periods of lifts (`New.Exchange.modLift`) to the periods of transposed
  lifts (`New.Exchange.modTransposedLift`).

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to diag(s) at the infinite places (s the signs) and 1 at the finite places.
* `New.IsEdge`: a relation between kernels e, e' on the two real groups and a Fock vector Φ. The
  kernel e is a cusp kernel and the doubling zeta integral of Φ against ē is not zero. For a form of
  type e, the lift with Φ is a form of type e' if it has a level, and for a polynomial v the lift
  with v is the convolution of the lift with Φ by some α ∈ C_c. The same holds with the groups
  exchanged and the kernels ē', ē.
* `New.IsArrow`: the datum φ is an arrow e → e' for the theta kernel K if forms of type e on S are
  rapid and their lifts by φ are forms of type e' on T.
* `New.Space.Form`: `S.Form e` is the space of bounded automorphic functions on the group of `S`
  that right convolution with `e` fixes (when `e` is integrable).
* `New.modKernel`: the theta kernel of the datum `New.modDatum` made of the Fock vector of a
  polynomial and a function on matrices modulo `𝔪`. Along an edge the lift and the transposed lift
  integrate a form against this kernel, in the first and in the second variable.

## Relation to the literature

Known result: Seesaw identity for periods of theta lifts. Here the statement holds for two unitary
pairs whose kernels agree up to moderate factors for a spanning set of Fock polynomials. Both pairs
carry edge families (`IsEdgeFamily`), and the data are taken modulo an ideal. If finite sums of
periods of the lift are proportional to a fixed family of numbers at all real translates, then so
are those of the transposed lift. Source: S. Kudla, Seesaw dual reductive pairs, in Automorphic
forms of several variables (Katata 1983), Progr. Math. 46, Birkhäuser 1984, 244–268.

See also `Lib.Weil.Lift`.
-/

noncomputable section

namespace New.Exchange

open NumberField CompactlySupported Space Fock

variable {E n n' : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n']
  (l : InfinitePlace E → n → ℤ) (s : n → ℤˣ) {s' : n' → ℤˣ}

/-- The pair of kernels `New.typeKernel` (products of discrete series kernels over the infinite
places): the one of the parameter `l` at `false` and the one of `-l` at `true`
(see `New.negIf`). -/
def kernelPair (d : Bool) : GInf E s → ℂ := typeKernel (negIf d l) s

variable {l} {l' : InfinitePlace E → n' → ℤ} {s} (S : Space E n s) (T : Space E n' s')
  (a : ∀ (n : Type) [Fintype n], AutChar E)
  {𝔪 : Modulus E} (P : MvPolynomial (InfinitePlace E × n' × n) ℂ)
    (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)

/-- The theta lift of forms of type e on S to type e′ on T, for the characters `a n`, `a n'` and the
datum of the polynomial P and Ψ mod 𝔪. It is a chosen linear map (`formLift`) that equals the lift
integral whenever the lifts are forms of type e′. -/
abbrev modLift (e : GInf E s → ℂ) (e' : GInf E s' → ℂ) : S.Form e →ₗ[ℂ] T.Form e' :=
  formLift (pairThetaKer S T (a n) (a n')) e e'
    (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P))

/-- The transposed lift of forms of type e′ on T to forms of type e on S, for the same kernel and
datum as `New.Exchange.modLift`. No complex conjugation enters. -/
abbrev modTransposedLift (e' : GInf E s' → ℂ) (e : GInf E s → ℂ) : T.Form e' →ₗ[ℂ] S.Form e :=
  formLift (pairThetaKer S T (a n) (a n')).swap e' e
    (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P))

variable {S T P Ψ} {I : Type*} (a : I → ∀ (n : Type) [Fintype n], AutChar E)
  (k : Bool → GInf E s → ℂ) (k' : Bool → GInf E s' → ℂ)

/-- Let k, k' be integral finite points of the two unitary groups and x = k'⁻¹yk modulo 𝔪, where
`𝔪.reductionGL` is the reduction modulo 𝔪 (if the proof `hx` of this equation is omitted, it is
sought by `simp; rfl`). Let v be a real Fock vector and vac the vacuum outside 𝔪. For characters a,
b the representation `pairWeil` at (k, k') sends the datum v ⊗ 1_x ⊗ vac to a(det k') b(det k)⁻¹
(the value of `pairChar`) times the datum v ⊗ 1_y ⊗ vac. -/
theorem pairWeil_modDatum_single {a b : AutChar E} {x y : Matrix n' n 𝔪.ResidueRing}
    {v : Heisenberg.IsVacuum.Model (realHeisenberg (realSigns E (homSigns s s')))}
      (k : stdLevel E n)
    (k' : stdLevel E n') (hx : x = (𝔪.reductionGL k')⁻¹.val * y * (𝔪.reductionGL k).val := by
      simp
      rfl) :
    let g := ((1, k.val), 1, k'.val)
    pairWeil S T a b g (modDatum S T 𝔪 (Pi.single x 1) v) =
      pairChar a b g • modDatum S T 𝔪 (Pi.single y 1) v := by
  -- By `pairWeil_modDatum_stdLevel` the indicator of `x` is precomposed with `m ↦ k'⁻¹ * m * k`
  -- modulo `𝔪`.
  have h_single : (fun m : Matrix n' n 𝔪.ResidueRing ↦ (Pi.single x 1 : _ → ℂ)
      ((𝔪.reductionGL k')⁻¹.val * m * (𝔪.reductionGL k).val)) = Pi.single y 1 := by
    ext m
    simp [hx, Pi.single_apply, Matrix.mul_left_inj_of_invertible,
      Matrix.mul_right_inj_of_invertible]
  intro g
  rw [pairWeil_modDatum_stdLevel, h_single]
  simp [g]

/-- The two functions k(false), k(true) on G_∞ are complex conjugates of each other, and each
satisfies `New.IsCuspKernel` of order 0. -/
def IsConjKernelPair : Prop := ∀ d : Bool, IsCuspKernel 0 (k d) ∧ k (!d) = star (k d)

/-- A family of characters `a i` over one real edge. (a) `k` and `k'` are pairs of conjugate
cuspidal types (`New.Exchange.IsConjKernelPair`); (b) all `a i n` have one weight `γ` and all
`a i n'` one weight `γ'`, and for each `i` both have the same tame part `ψ i`, which may vary with
`i`; (c) for the real Weil representation of weights `γ`, `γ'`, the types `k d`, `k' d` and the Fock
vector of the polynomial `Φ` form an edge in the sense of `New.IsEdge`. -/
def IsEdgeFamily (d : Bool) (Φ : MvPolynomial (InfinitePlace E × n' × n) ℂ) : Prop :=
  IsConjKernelPair k ∧ IsConjKernelPair k' ∧
  ∃ (γ γ' : InfinitePlace E → ℤ) (ψ : I → (w : FinPlace E) → MulChar (ResField w) ℂ),
    (∀ i : I, (a i n).HasWeight γ (ψ i)) ∧ (∀ i : I, (a i n').HasWeight γ' (ψ i)) ∧
    New.IsEdge (realPairWeil γ γ') (k d) (k' d) (polyVector (realSigns E (homSigns s s')) Φ)

omit [WeilData E] in
/-- Let `n` be nonempty and `l` an integer parameter at each infinite place. If the Harish-Chandra
parameter `toHCParam s` of `negIf d l` (which is `-l` if `d` is true and `l` otherwise) has a large
gap (`HasLargeGap 0`) at every infinite place, the kernels of `l` and `-l` are cuspidal and
conjugate to each other. -/
theorem isConjKernelPair_kernelPair {d : Bool} [Nonempty n]
    (h_gap_d : ∀ w : InfinitePlace E, (toHCParam s (negIf d l w)).HasLargeGap 0) :
    IsConjKernelPair (kernelPair l s) := by
  -- Both `l` and `-l` have the gap that makes the type cuspidal; by `conj_dsKernel_neg` their
  -- kernels are conjugate.
  have h_gap (w : InfinitePlace E) : (toHCParam s (l w)).HasLargeGap 0 := by
    cases d
    · exact h_gap_d w
    · simpa [HCParam.HasLargeGap] using (h_gap_d w).neg
  have h_conj : typeKernel l s = star (typeKernel (-l) s) :=
    funext fun x ↦ by simp [typeKernel, ← conj_dsKernel_neg (h_gap _)]
  rintro (_ | _)
  · exact ⟨isCuspKernel_typeKernel h_gap, eq_star_of_eq_star h_conj⟩
  · exact ⟨isCuspKernel_typeKernel fun w ↦ (h_gap w).neg, h_conj⟩

/-- Suppose the parameters `negIf d l`, `negIf d l'` (that is `±l`, `±l'`, with the sign `-` for
`d = true`) correspond for the weights `γ`, `γ'` (`New.ParamsCorrespond`). Suppose the characters
`a i n` have the weight `γ`, the characters `a i n'` have the weight `γ'`, and both have the tame
part `ψ i`. Then the `a i` form an edge family: the types are the kernels of `±l`, `±l'`, and the
polynomial is the product over the infinite places of chosen joint harmonics. -/
theorem isEdgeFamily_of_paramsCorrespond [Nonempty n] [Nonempty n'] {γ γ' : InfinitePlace E → ℤ}
    {ψ : I → (w : FinPlace E) → MulChar (ResField w) ℂ} (d : Bool)
    (hγ : ∀ i : I, (a i n).HasWeight γ (ψ i)) (hγ' : ∀ i : I, (a i n').HasWeight γ' (ψ i))
    (h_corr : ParamsCorrespond γ γ' (negIf d l) (negIf d l') s s') :
    IsEdgeFamily a (kernelPair l s) (kernelPair l' s') d
      (jointHarmonic γ γ' (negIf d l) (negIf d l') s s') := by
  have h_gap (w : InfinitePlace E) : (toHCParam s (negIf d l w)).HasLargeGap 0 := by
    -- matching gives the gap for the negative of this parameter
    simpa [HCParam.HasLargeGap] using ((h_corr.isMatch w).swap.hasLargeGap (Nat.zero_le _)).neg
  have h_gap' (w : InfinitePlace E) : (toHCParam s' (negIf d l' w)).HasLargeGap 0 :=
    (h_corr.isMatch w).hasLargeGap (Nat.zero_le _)
  exact ⟨isConjKernelPair_kernelPair h_gap, isConjKernelPair_kernelPair h_gap', γ, γ', ψ, hγ, hγ',
    h_corr.isEdge_jointHarmonic⟩

/-! ### Pairs with two separately given characters -/

section Pair

/-- The theta lift of forms of type `e` on `S` to forms of type `e'` on `T`, for characters
`a`, `b` (entering as a(det h) b(det g)⁻¹ for g on `S`, h on `T`) and the datum of the polynomial
`P` and the function `Ψ` modulo `𝔪`.
It is a chosen linear map (`formLift`) that equals the lift integral along an edge
(`New.Exchange.IsPairEdge.isArrow_lift`). -/
abbrev pairLift (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (e : GInf E s → ℂ) (e' : GInf E s' → ℂ) : S.Form e →ₗ[ℂ] T.Form e' :=
  formLift (pairThetaKer S T a b) e e'
    (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P))

/-- The transposed lift of forms of type `e'` on `T` to forms of type `e` on `S`, for the kernel
and the datum of `New.Exchange.pairLift`. No complex conjugation enters. It equals the integral
along an edge between the conjugate types (`New.Exchange.IsPairEdge.isArrow_swap`). -/
abbrev pairTransposedLift (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ)
    (e' : GInf E s' → ℂ) (e : GInf E s → ℂ) : T.Form e' →ₗ[ℂ] S.Form e :=
  formLift (pairThetaKer S T a b).swap e' e
    (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P))

/-- Characters `a i`, `b i` over one real edge: each `a i` has weight `γ` and each `b i` has weight
`γ'`, with some tame parts that may depend on `i`, and the types `e`, `e'` with the Fock vector of
`P` form an edge (`New.IsEdge`) for the weights `γ`, `γ'`. -/
def IsPairEdge (a b : I → AutChar E) (e : GInf E s → ℂ) (e' : GInf E s' → ℂ)
    (P : MvPolynomial (InfinitePlace E × n' × n) ℂ) : Prop :=
  ∃ γ γ' : InfinitePlace E → ℤ,
    (∀ i : I, ∃ ψ : (w : FinPlace E) → MulChar (ResField w) ℂ, (a i).HasWeight γ ψ) ∧
    (∀ i : I, ∃ ψ : (w : FinPlace E) → MulChar (ResField w) ℂ, (b i).HasWeight γ' ψ) ∧
    IsEdge (realPairWeil γ γ') e e' (polyVector (realSigns E (homSigns s s')) P)

variable {a b : I → AutChar E} {e : GInf E s → ℂ} {e' : GInf E s' → ℂ}

/-- Let the characters `a i` have weight `γ` and the `b i` weight `γ'`, with some tame parts. If at
each infinite place `w` the polynomial `Φ w` is a joint harmonic for the parameters `l'`, `-l` and
the weights `γ`, `-γ'` (`New.IsJointHarmonic`), then the product of the `Φ w`, each in the variables
of `w`, gives an edge (`New.Exchange.IsPairEdge`) between the types of `l` and `l'`. This is a
corollary of `New.isEdge_of_isJointHarmonic`. -/
lemma isPairEdge_of_isJointHarmonic [Nonempty n] [Nonempty n'] {γ γ' : InfinitePlace E → ℤ}
    (ha : ∀ i : I, ∃ ψ : (w : FinPlace E) → MulChar (ResField w) ℂ, (a i).HasWeight γ ψ)
    (hb : ∀ i : I, ∃ ψ : (w : FinPlace E) → MulChar (ResField w) ℂ, (b i).HasWeight γ' ψ)
    {Φ : InfinitePlace E → MvPolynomial (n' × n) ℂ}
    (hΦ : ∀ w : InfinitePlace E, IsJointHarmonic (.std s' s (γ w) (-γ' w)) (l' w) (-l w) (Φ w)) :
    IsPairEdge a b (typeKernel l s) (typeKernel l' s')
      (∏ w : InfinitePlace E, MvPolynomial.rename (fun p : n' × n ↦ (w, p)) (Φ w)) :=
  ⟨γ, γ', ha, hb, isEdge_of_isJointHarmonic hΦ⟩

/-- An edge family (`New.Exchange.IsEdgeFamily`) of characters `c` with polynomial `P` is an edge
(`New.Exchange.IsPairEdge`) between `k d` and `k' d` for the characters that `c` attaches to the
index types `n`, `n'`. -/
lemma IsEdgeFamily.isPairEdge {c : I → ∀ (m : Type) [Fintype m], AutChar E}
    {k : Bool → GInf E s → ℂ} {k' : Bool → GInf E s' → ℂ} {d : Bool}
    (hP : IsEdgeFamily c k k' d P) :
    IsPairEdge (fun i : I ↦ c i n) (fun i : I ↦ c i n') (k d) (k' d) P :=
  have ⟨_, _, γ, γ', ψ, hγ, hγ', h_edge⟩ := hP
  ⟨γ, γ', fun i ↦ ⟨ψ i, hγ i⟩, fun i ↦ ⟨ψ i, hγ' i⟩, h_edge⟩

/-- An edge family of characters `c` with polynomial `P` is an edge between `star (k !d)` and
`star (k' !d)`, the conjugates of the opposite types, which equal `k d` and `k' d`. -/
lemma IsEdgeFamily.isPairEdge_star {c : I → ∀ (m : Type) [Fintype m], AutChar E}
    {k : Bool → GInf E s → ℂ} {k' : Bool → GInf E s' → ℂ} {d : Bool}
    (hP : IsEdgeFamily c k k' d P) :
    IsPairEdge (fun i : I ↦ c i n) (fun i : I ↦ c i n') (star (k !d)) (star (k' !d)) P := by
  have ⟨hk, hk', _⟩ := hP
  simpa only [(hk d).right, (hk' d).right, star_star] using hP.isPairEdge

/-- The source type `e` of an edge is a cusp kernel of order 0. -/
lemma IsPairEdge.isCuspKernel (hP : IsPairEdge a b e e' P) : IsCuspKernel 0 e :=
  have ⟨_, _, _, _, h_edge⟩ := hP
  h_edge.isCuspKernel_source

/-- The conjugate of the target type `e'` of an edge is a cusp kernel of order 0. -/
lemma IsPairEdge.isCuspKernel_star (hP : IsPairEdge a b e e' P) : IsCuspKernel 0 (star e') :=
  have ⟨_, _, _, _, h_edge⟩ := hP
  h_edge.swapped.isCuspKernel_source

/-- Along an edge, the datum of `P` and `Ψ` lifts forms of type `e` to forms of type `e'`, and its
transposed lift takes forms of the conjugate type of `e'` to the conjugate type of `e`. -/
lemma IsPairEdge.isArrow (hP : IsPairEdge a b e e' P) (i : I) :
    IsArrow (pairThetaKer S T (a i) (b i)) e e'
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) ∧
    IsArrow (pairThetaKer S T (a i) (b i)).swap (star e') (star e)
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) := by
  obtain ⟨γ, γ', ha, hb, h_edge⟩ := hP
  -- the weights of `a i` and `b i` are used as instances
  obtain ⟨ψ, hψ⟩ := ha i
  obtain ⟨ψ', hψ'⟩ := hb i
  exact h_edge.isArrow (a i) (b i) (schrodingerOp_mem_finitePart _ _)

/-- Along an edge, the datum of `P` and `Ψ` lifts forms of type `e` on `S` to forms of type `e'`
on `T`. -/
lemma IsPairEdge.isArrow_lift (hP : IsPairEdge a b e e' P) (S : Space E n s) (T : Space E n' s')
    (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (i : I) :
    IsArrow (pairThetaKer S T (a i) (b i)) e e'
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) :=
  (hP.isArrow i).left

/-- Along an edge from `e` to `e'`, the transposed lift by the datum of `P` and `Ψ` takes forms of
the conjugate type of `e'` on `T` to forms of the conjugate type of `e` on `S`. -/
lemma IsPairEdge.isArrow_swap_star (hP : IsPairEdge a b e e' P) (S : Space E n s)
    (T : Space E n' s') (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (i : I) :
    IsArrow (pairThetaKer S T (a i) (b i)).swap (star e') (star e)
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) :=
  (hP.isArrow i).right

/-- Suppose the characters `a i`, `b i`, the conjugate types `star e`, `star e'` and the polynomial
`P` form an edge (`New.Exchange.IsPairEdge`). Let v_P be the Fock vector of `P`. Then for each `i`,
the datum v_P ⊗ Ψ ⊗ vac on Hom(S, T) (real part v_P, the lift of Ψ : matrices mod 𝔪 → ℂ at the
places dividing 𝔪, vacuum elsewhere) is an arrow e' → e for the swapped theta kernel of `S`, `T`,
`a i`, `b i`. That is, forms of type `e'` on the group of `T` are rapid, and their transposed lifts
are forms of type `e` on the group of `S`. -/
lemma IsPairEdge.isArrow_swap (hP : IsPairEdge a b (star e) (star e') P) (i : I) :
    IsArrow (pairThetaKer S T (a i) (b i)).swap e' e
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) := by
  simpa only [star_star] using hP.isArrow_swap_star S T Ψ i

/-- For an edge with polynomial `P` and any polynomial `Q` there is one continuous function `α` of
compact support on the real points of the target such that, for all finite data, the lift formed
with `Q` is the right convolution by `α` of the lift formed with `P`. -/
lemma IsPairEdge.exists_lift_eq_realConv (hP : IsPairEdge a b e e' P)
    (Q : MvPolynomial (InfinitePlace E × n' × n) ℂ) :
    ∃ α : C_c(GInf E s', ℂ), ∀ (i : I) (S : Space E n s) (T : Space E n' s') (𝔪 : Modulus E)
      (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (y : S.Form e),
      lift (pairThetaKer S T (a i) (b i))
          (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) Q)) y =
        realConv α (pairLift S T (a i) (b i) P Ψ e e' y) := by
  -- The same `α` serves for every theta kernel with real part `realPairWeil γ γ'`, so for all data.
  have ⟨γ, γ', ha, hb, h_edge⟩ := hP
  obtain ⟨α, hα⟩ := h_edge.exists_lift_eq_realConv _ ⟨Q, rfl⟩
  refine ⟨α, fun i S T 𝔪 Ψ y ↦ ?_⟩
  -- the weights of `a i` and `b i` are used as instances
  obtain ⟨ψ, hψ⟩ := ha i
  obtain ⟨ψ', hψ'⟩ := hb i
  rw [(hP.isArrow_lift S T Ψ i).coe_formLift]
  exact hα _ (pairWeil_integrated S T (a i) (b i)) y.prop

variable (T) in
omit [WeilData E] in
/-- Real averages against `α` and `β` multiply the pairing of forms of conjugate cuspidal types by
one number. -/
lemma exists_integral_realConv_mul_realConv (he' : IsCuspKernel 0 (star e'))
    (α β : C_c(GInf E s', ℂ)) :
    ∃ r : ℂ, ∀ (y : T.Form e') (y' : T.Form (star e')),
      ∫ g : G E s', realConv α y g * realConv β y' g ∂T.quotMeasure =
        r * ∫ g : G E s', y g * y' g ∂T.quotMeasure := by
  refine ⟨∫ x, ∫ z, α x * β z * (e' (x⁻¹ * z) / star (e' 1)), fun y y' ↦ ?_⟩
  -- The left side is the Petersson product of the averages of the conjugate of `y` and of `y'`.
  simpa [petersson, realConv, ← integral_conj] using (conjForm rfl y).prop
    |>.petersson_realConv_realConv he' y'.prop (star α).integrable β.integrable

end Pair

/-! ### Lifts along an edge family -/

variable {a k k'} {d : Bool}

omit [WeilData E] in
/-- A form of a type from a conjugate cuspidal pair decreases rapidly. -/
lemma IsConjKernelPair.form_mem_rapidFunctions (hk : IsConjKernelPair k) (y : S.Form (k d)) :
    y.val ∈ S.rapidFunctions :=
  y.prop.mem_rapidFunctions (hk d).left

/-- Along an edge, the datum with the Fock vector of `P` at infinity and any finite part `Ψ` modulo
`𝔪` lifts forms of type `k d` on `S` to forms of type `k' d` on `T` (see `New.IsArrow`). -/
theorem IsEdgeFamily.isArrow_lift (hP : IsEdgeFamily a k k' d P) (S : Space E n s)
    (T : Space E n' s') (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (i : I) :
    IsArrow (pairThetaKer S T (a i n) (a i n')) (k d) (k' d)
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) :=
  hP.isPairEdge.isArrow_lift S T Ψ i

/-- Along an edge, the transposed lift by the datum of `P` and `Ψ` takes forms of the conjugate type
`k' (!d)` on `T` to forms of type `k (!d)` on `S` (see `New.IsArrow`). -/
theorem IsEdgeFamily.isArrow_swap (hP : IsEdgeFamily a k k' d P) (S : Space E n s)
    (T : Space E n' s') (Ψ : Matrix n' n 𝔪.ResidueRing → ℂ) (i : I) :
    IsArrow (pairThetaKer S T (a i n) (a i n')).swap (k' !d) (k !d)
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) := by
  have ⟨hk, hk', _⟩ := hP
  -- The types `k (!d)` and `k' (!d)` are the conjugates of `k d` and `k' d`.
  simpa only [(hk d).right, (hk' d).right] using hP.isPairEdge.isArrow_swap_star S T Ψ i

/-- Along an edge, the datum of `P` and `Ψ` lifts forms of type `k d` on `S` to forms of type `k' d`
on `T`, and its transposed lift takes forms of type `k' (!d)` on `T` to forms of type `k (!d)` on
`S`. -/
theorem IsEdgeFamily.isArrow_modDatum (hP : IsEdgeFamily a k k' d P) {i : I} :
    IsArrow (pairThetaKer S T (a i n) (a i n')) (k d) (k' d)
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) ∧
    IsArrow (pairThetaKer S T (a i n) (a i n')).swap (k' !d) (k !d)
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s s')) P)) :=
  ⟨hP.isArrow_lift S T Ψ i, hP.isArrow_swap S T Ψ i⟩

/-- For an edge with polynomial `P` and any polynomial `Q` there is one continuous compactly
supported function `α` on the real points of the target group such that, for all finite data, the
lift formed with `Q` is the right convolution by `α` of the lift formed with `P`. -/
theorem IsEdgeFamily.exists_lift_eq_realConv (h : IsEdgeFamily a k k' d P)
    (Q : MvPolynomial (InfinitePlace E × n' × n) ℂ) :
    ∃ α : C_c(GInf E s', ℂ), ∀ (i : I) (S : Space E n s) (T : Space E n' s') (𝔪 : Modulus E)
      (x : Matrix n' n 𝔪.ResidueRing → ℂ) (y : S.Form (k d)),
      lift (pairThetaKer S T (a i n) (a i n'))
          (modDatum S T 𝔪 x (polyVector (realSigns E (homSigns s s')) Q)) y.val =
        realConv α (modLift S T (a i) P x (k d) (k' d) y) :=
  h.isPairEdge.exists_lift_eq_realConv Q

/-- Let `a` be an edge family (`IsEdgeFamily a k k' d P`: characters `a i` over one real edge with
cuspidal types `k`, `k'`) and let `Q` be any polynomial. Then there is one `κ` that works for all
`i`, spaces `S`, `T`, modulus `𝔪`, functions `x` on residue matrices, and forms `y : S.Form (k !d)`,
`z : T.Form (k' !d)`. Take the Petersson product on `T` of `z` with the conjugate of the theta lift
of `star y`, whose kernel is `pairThetaKer` for `a i` and whose datum is `modDatum` of `x` and the
Fock vector of `Q`. It equals `κ` times the inner product of `modTransposedLift` of `z` (formed with
`P`, `x`) with `y`. -/
theorem IsEdgeFamily.petersson_lift_eq_mul_inner_modTransposedLift (h : IsEdgeFamily a k k' d P)
    (Q : MvPolynomial (InfinitePlace E × n' × n) ℂ) :
    ∃ κ : ℂ, ∀ (i : I) (S : Space E n s) (T : Space E n' s') (𝔪 : Modulus E)
      (x : Matrix n' n 𝔪.ResidueRing → ℂ) (y : S.Form (k !d)) (z : T.Form (k' !d)),
      T.petersson z.val (star (lift (pairThetaKer S T (a i n) (a i n'))
          (modDatum S T 𝔪 x (polyVector (realSigns E (homSigns s s')) Q)) (star y.val))) =
        κ * inner ℂ (modTransposedLift S T (a i) P x (k' !d) (k !d) z) y := by
  -- Conjugate the identity of `IsEdge.exists_petersson_lift_eq_mul` for the conjugate forms, and
  -- pass from the lift with `P` to its adjoint.
  have ⟨hk, hk', γ, γ', ψ, hγ, hγ', h_edge⟩ := h
  obtain ⟨κ, hκ⟩ := h_edge.exists_petersson_lift_eq_mul
  refine ⟨star (κ Q), fun i S T 𝔪 x y z ↦ ?_⟩
  have ⟨hk_star, hk'_star⟩ : k (!d) = star (k d) ∧ k' (!d) = star (k' d) :=
    ⟨(hk d).right, (hk' d).right⟩
  let y' : S.Form (k d) := conjForm (eq_star_of_eq_star hk_star) y
  let z' : T.Form (k' d) := conjForm (eq_star_of_eq_star hk'_star) z
  let w : T.Form (k' !d) := conjForm hk'_star (modLift S T (a i) P x (k d) (k' d) y')
  let liftBy (R : MvPolynomial (InfinitePlace E × n' × n) ℂ) : G E s' → ℂ :=
    lift (pairThetaKer S T (a i n) (a i n'))
      (modDatum S T 𝔪 x (polyVector (realSigns E (homSigns s s')) R)) y'
  have h_adj : inner ℂ (modTransposedLift S T (a i) P x (k' !d) (k !d) z) y = T.petersson z w :=
    (h.isArrow_swap S T x i).inner_formLift_adjoint (h.isArrow_lift S T x i)
      (eq_star_of_eq_star hk_star) hk'_star y z
  have h_conj (F : G E s' → ℂ) : T.petersson z.val (star F) = star (T.petersson z' F) := by
    simp [z', petersson, ← integral_conj]
  have h_w : w.val = star (liftBy P) := congrArg star ((h.isArrow_lift S T x i).coe_formLift y')
  have h_scale : T.petersson z' (liftBy Q) = κ Q * T.petersson z' (liftBy P) :=
    (hκ (a i n) (a i n') (schrodingerOp_mem_finitePart _ _) Q y' z').1
  change T.petersson z.val (star (liftBy Q)) = _
  rw [h_adj, h_w, h_conj, h_conj, h_scale, star_mul']

end New.Exchange

/-! ## Periods of two forms and the seesaw between lift and transposed lift -/

namespace New

open MeasureTheory Matrix Submodule Set Fintype Space Fock Exchange

variable {E n m n' m' : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m']
  {s : n → ℤˣ} {t : m → ℤˣ} {s' : n' → ℤˣ} {t' : m' → ℤˣ} {S : Space E n s} {T : Space E m t}
  {S' : Space E n' s'} {T' : Space E m' t'}

/-- Relabelling the coordinates of a hermitian space along a bijection `e` that carries the signs
`s` to `t` preserves the height of group elements. -/
lemma Space.height_reindex (e : n ≃ m) (he : s ∘ e.symm = t) (g : G E s) :
    (S.reindex e he).height (G.reindex (t := t) e he g) = S.height g := by
  -- Relabelling vectors along `e` matches the two lattices and preserves the Euclidean norm.
  let V := S.move g
  let V' := (S.reindex e he).move (G.reindex (t := t) e he g)
  have h_vec (ξ : n → E) : V'.vecAtPoint (ξ ∘ e.symm) = V.vecAtPoint ξ ∘ e.symm := by
    simp [V, V', ↓vecAtPoint_move, vecAtPoint, reindex, ← map_inv, mulVec_eq_sum, reindex_equiv e,
      funext_iff]
  have h_mem (ξ : n → E) : ξ ∘ e.symm ∈ V'.baseLattice ↔ ξ ∈ V.baseLattice := by
    simp [baseLattice, h_vec, reindex_equiv e]
  have h_norm (ξ : n → E) : ‖V'.archCoords (ξ ∘ e.symm)‖ = ‖V.archCoords ξ‖ := by
    simp [archCoords, h_vec, PiLp.norm_eq_of_L2, sum_prod_type, reindex_equiv e]
  suffices h_min : V'.firstMinimum = V.firstMinimum from congrArg (·⁻¹) h_min
  simp only [firstMinimum, image, reindex_equiv (e.piCongrLeft' fun _ ↦ E)]
  simp [show ∀ ξ, e.piCongrLeft' (fun _ ↦ E) ξ = ξ ∘ e.symm from fun _ ↦ rfl, h_mem, h_norm,
    funext_iff, reindex_equiv e]

/-- Let the types `k` form a conjugate cuspidal pair. The product of the moderate weight
`w.weightFn`, a form of type `k d` on `S` (which decreases rapidly) and a form on `T`, read along
`w.comparisonMap` and moved by `r`, is integrable. -/
lemma Space.integrable_moderate_mul_forms {k : Bool → GInf E s → ℂ} {d : Bool} {e : GInf E t → ℂ}
    {r : G E t} (hk : IsConjKernelPair k) (w : S.ModerateWeight T) (f : S.Form (k d))
    (y : T.Form e) :
    Integrable (fun z : G E s ↦ w.weightFn z * f z * y (w.comparisonMap z * r)) S.quotMeasure := by
  -- the rapid `f` times the moderate weight is integrable, and `y` is bounded
  have h_int : Integrable (⇑w.weightFn * f.val) S.quotMeasure :=
    ((hk.form_mem_rapidFunctions f).right.mul w.isModerate).integrable
      (w.weightFn.continuous.mul f.prop.continuous)
  exact y.prop.isBoundedMeasurable.integrable_mul_comp h_int fun z : G E s ↦ w.comparisonMap z * r

variable [WeilData E]

/-- The integral over the quotient of the group of `S` of the weight, a form on `S`, and a form on
`T` that is pulled back along `w.comparisonMap` and translated by the real point `r`. -/
noncomputable def Space.periodPairing {k : Bool → GInf E s → ℂ} {d : Bool} {e : GInf E t → ℂ}
    (h : IsConjKernelPair k) (w : S.ModerateWeight T) (r : GInf E t) :
    S.Form (k d) →ₗ[ℂ] T.Form e →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun f y ↦ ∫ z : G E s, w.weightFn z * f z * y (w.comparisonMap z * (r, 1)) ∂S.quotMeasure)
    -- additivity needs the integrability `integrable_moderate_mul_forms` of the two summands
    (fun f f' y ↦ by
      simp [show (f + f').val = f.val + f'.val from rfl, integrable_moderate_mul_forms h w,
        ← integral_add, mul_add, add_mul])
    (fun c f y ↦ by
      simp [show (c • f).val = c • f.val from rfl, ← integral_const_mul, mul_assoc, mul_left_comm])
    (fun f y y' ↦ by
      simp [show (y + y').val = y.val + y'.val from rfl, integrable_moderate_mul_forms h w,
        ← integral_add, mul_add])
    (fun c f y ↦ by
      simp [show (c • y).val = c • y.val from rfl, ← integral_const_mul, mul_left_comm])

/-- The types `k` on the source of an edge family form a pair of conjugate cuspidal types. -/
lemma Exchange.IsEdgeFamily.isConjKernelPair_source {I : Type*}
    {a : I → ∀ (n : Type) [Fintype n], AutChar E} {k : Bool → GInf E s → ℂ}
    {k' : Bool → GInf E t → ℂ} {d : Bool}
    {P : MvPolynomial (NumberField.InfinitePlace E × m × n) ℂ} (h : IsEdgeFamily a k k' d P) :
    IsConjKernelPair k :=
  h.left

/-- The types `k'` on the target of an edge family form a pair of conjugate cuspidal types. -/
lemma Exchange.IsEdgeFamily.isConjKernelPair_target {I : Type*}
    {a : I → ∀ (n : Type) [Fintype n], AutChar E} {k : Bool → GInf E s → ℂ}
    {k' : Bool → GInf E t → ℂ} {d : Bool}
    {P : MvPolynomial (NumberField.InfinitePlace E × m × n) ℂ} (h : IsEdgeFamily a k k' d P) :
    IsConjKernelPair k' :=
  h.right.left

section

variable {k : Bool → GInf E s → ℂ} {k' : Bool → GInf E s' → ℂ} {d d' : Bool}

/-- For moderate weight `N` and forms `y` on `S` and `f` on `S'` whose types belong to conjugate
cuspidal pairs, the product of `N`, `y`, the theta kernel of `T'` and `S'` with datum `φ` and `f` is
integrable on the product of the two quotients. -/
lemma Exchange.integrable_kernel_mul_forms (hk : IsConjKernelPair k) (hk' : IsConjKernelPair k')
    (a b : AutChar E) (N : S.ModerateWeight T') (y : S.Form (k d)) (f : S'.Form (k' d'))
    (φ : 𝒮 (T'.hom S')) :
    Integrable (fun p : G E s × G E s' ↦ N.weightFn p.1 * y p.1 *
        ((T'.hom S').θ (pairWeil T' S' a b (N.comparisonMap p.1, p.2) φ) * f p.2))
      (S.quotMeasure.prod S'.quotMeasure) :=
  (pairThetaKer T' S' a b).swap.integrable_prod_weightFn (hk'.form_mem_rapidFunctions f) N
    (hk.form_mem_rapidFunctions y) φ

/-- Let `k`, `k'` be pairs of conjugate cuspidal types (`New.Exchange.IsConjKernelPair`), `y` a form
of type `k d` on `S` and `f` a form of type `k' d'` on `S'`. Let `N` be a moderate weight, with a
function on the group of `S` and a map from it to the group of `T'`. For a Fock vector `v` let θ_v
be the theta kernel of the pair `T'`, `S'` for the characters `a`, `b` and the datum
`modDatum T' S' 𝔪 Ψ v`, made of `v` at infinity and `Ψ` modulo `𝔪`. Then the integral of
`N.weightFn g * y g * θ_v (N.comparisonMap g, x) * f x` over `x` and `g` in the quotients of the
groups of `S'` and `S` is a continuous linear function of `v`. -/
lemma Exchange.exists_continuousLinearMap_eq_integral_kernel_mul_forms
    (hk : IsConjKernelPair k) (hk' : IsConjKernelPair k') (a b : AutChar E) {𝔪 : Modulus E}
    (Ψ : Matrix n' m' 𝔪.ResidueRing → ℂ) (N : S.ModerateWeight T') (y : S.Form (k d))
    (f : S'.Form (k' d')) :
    ∃ L : fockSpace (realSigns E (homSigns t' s')) →L[ℂ] ℂ,
      ∀ v : fockSpace (realSigns E (homSigns t' s')),
        L v = ∫ g : G E s, ∫ x : G E s', N.weightFn g * y g *
            ((T'.hom S').θ (pairWeil T' S' a b (N.comparisonMap g, x) (modDatum T' S' 𝔪 Ψ v)) * f x)
          ∂S'.quotMeasure ∂S.quotMeasure := by
  -- The integrand is a family `F` of bounded functionals of the datum, integrable at each datum, so
  -- its integral is a bounded functional. The datum is a continuous linear function `D` of `v`.
  let F (p : G E s × G E s') : 𝒮 (T'.hom S') →L[ℂ] ℂ := (N.weightFn p.1 * y p.1) •
    (T'.hom S').θ.smulRight (f p.2) ∘L pairWeil T' S' a b (N.comparisonMap p.1, p.2)
  have F_apply (p : G E s × G E s') (φ : 𝒮 (T'.hom S')) : F p φ = N.weightFn p.1 * y p.1 *
      ((T'.hom S').θ (pairWeil T' S' a b (N.comparisonMap p.1, p.2) φ) * f p.2) := rfl
  have F_int (φ : 𝒮 (T'.hom S')) :
      Integrable (fun p : G E s × G E s' ↦ F p φ) (S.quotMeasure.prod S'.quotMeasure) :=
    integrable_kernel_mul_forms hk hk' a b N y f φ
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : 𝒮 (T'.hom S') →L[ℂ] ℂ, ∀ φ : 𝒮 (T'.hom S'),
      Λ φ = ∫ p : G E s × G E s', F p φ ∂S.quotMeasure.prod S'.quotMeasure :=
    exists_continuousLinearMap_apply_eq_integral (S.quotMeasure.prod S'.quotMeasure) F F_int
  let D : fockSpace (realSigns E (homSigns t' s')) →L[ℂ] 𝒮 (T'.hom S') :=
    (T'.hom S').integrated.flip
      ((T'.hom S').schrodingerOp 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix)) (T'.hom S').vacElem)
  have D_apply (v : fockSpace (realSigns E (homSigns t' s'))) : D v = modDatum T' S' 𝔪 Ψ v := rfl
  refine ⟨Λ ∘L D, fun v ↦ ?_⟩
  -- by Fubini the integral over the product is the iterated integral
  rw [ContinuousLinearMap.comp_apply, D_apply, hΛ, integral_prod _ (F_int _)]
  simp only [F_apply]

variable {e : GInf E t → ℂ}

omit [WeilData E] in
/-- For a continuous `α` of compact support on the real points of the group of `T`, a moderate
weight `M` and a form `U` on `T`, the product of `α r`, `M`, `f` and `U` moved by `r` is
integrable in the two variables. -/
lemma Exchange.integrable_mul_weight_mul_forms (hk' : IsConjKernelPair k')
    (α : CompactlySupportedContinuousMap (GInf E t) ℂ) (M : S'.ModerateWeight T)
    (f : S'.Form (k' d')) (U : T.Form e) :
    Integrable (fun p : GInf E t × G E s' ↦
        α p.1 * (M.weightFn p.2 * f p.2 * U (M.comparisonMap p.2 * (p.1, 1))))
      (volume.prod S'.quotMeasure) := by
  have h_int : Integrable (⇑M.weightFn * f.val) S'.quotMeasure :=
    ((hk'.form_mem_rapidFunctions f).right.mul M.isModerate).integrable
      (M.weightFn.continuous.mul f.prop.continuous)
  simpa [mul_assoc] using U.prop.isBoundedMeasurable.integrable_mul_comp
    (α.integrable.mul_prod h_int) fun p : GInf E t × G E s' ↦ M.comparisonMap p.2 * (p.1, 1)

/-- The seesaw for one pair of forms. If the lift of `y` by the datum of `Q` is the average against
`α` of the real translates of `U`, and the weight `N` times the kernel of `p` with characters `a'`,
`b'` and finite datum `Ψ'` agrees with `M` times the kernel with `a`, `b`, `Ψ` of the lift, namely
the kernel of `Q`, then the double integral of `N`, `y`, `f` and the kernel of `p` is the average
against `α` of the periods with weight `M` of `f` against the translates of `U`. -/
lemma Exchange.integral_kernel_mul_forms_eq_integral_periodPairing
    (hk : IsConjKernelPair k) (hk' : IsConjKernelPair k') {a b a' b' : AutChar E} {𝔪 : Modulus E}
    {Ψ : Matrix m n 𝔪.ResidueRing → ℂ} {Ψ' : Matrix n' m' 𝔪.ResidueRing → ℂ}
    {N : S.ModerateWeight T'} {M : S'.ModerateWeight T}
    {Q : MvPolynomial (NumberField.InfinitePlace E × m × n) ℂ}
    {p : MvPolynomial (NumberField.InfinitePlace E × n' × m') ℂ}
    {y : S.Form (k d)} (f : S'.Form (k' d')) {U : T.Form e}
    {α : CompactlySupportedContinuousMap (GInf E t) ℂ}
    (h_lift : lift (pairThetaKer S T a b)
      (modDatum S T 𝔪 Ψ (polyVector (realSigns E (homSigns s t)) Q)) y = realConv α U)
    (h_kernel : ∀ (g : G E s) (x : G E s'),
      N.weightFn g * modKernel T' S' a' b' 𝔪 Ψ' p (N.comparisonMap g) x =
        M.weightFn x * modKernel S T a b 𝔪 Ψ Q g (M.comparisonMap x)) :
    ∫ g : G E s, ∫ x : G E s', N.weightFn g * y g *
        (modKernel T' S' a' b' 𝔪 Ψ' p (N.comparisonMap g) x * f x)
          ∂S'.quotMeasure ∂S.quotMeasure =
      ∫ r : GInf E t, α r * periodPairing hk' M r f U := by
  -- By Fubini the integral over `g` may be taken inside; by the kernel identity it is then the
  -- lift of `y` with datum `Q` at `M.comparisonMap x`.
  simp_rw [modKernel, pairTheta, periodPairing, LinearMap.mk₂_apply, ← integral_const_mul (α _)]
  rw [integral_integral_swap (integrable_kernel_mul_forms hk hk' a' b' N y f _), eq_comm,
    integral_integral_swap (integrable_mul_weight_mul_forms hk' α M f U)]
  simp_rw [mul_left_comm (α _), integral_const_mul, ← realConv.eq_1, ← h_lift, lift,
    ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun x ↦ integral_congr_ae (.of_forall fun g ↦ ?_))
  simp only [modKernel, pairTheta] at h_kernel
  linear_combination -(y.val g * f.val x) * h_kernel g x

end

/-- The polynomials `p` for the pair `T' → S'` that match the pair `S → T` in the seesaw
`New.Exchange.seesaw_periods`. The data are families indexed by `o : J` and `i : X o`: forms `y` on
`S` and `f` on `S'`, moderate weights `N` and finite data `Ψ'`, with `y` of type `e₁`, lifts of type
`e₂` on `T`, and characters `a o` for `S → T` and `a' o` for `T' → S'`; sums run over `W o` with
coefficients `u o`. The polynomial `p` matches if there are a polynomial `Q`, finite data `Ψ` and
moderate weights `M` with two properties. (a) For every real point, the sums of the periods with
weight `M` of `f` against the lifts of `y` by `Φ` and `Ψ`, moved by that point, are a multiple of
the vector `c`. (b) The weight of `N` times the kernel of `p` and `Ψ'` along the map of `N` equals
the weight of `M` times the kernel of `Q` and `Ψ` along the map of `M`. -/
def Exchange.IsSeesawMatched {J : Type*} {X : J → Type} {𝔪 : J → Modulus E}
    {e₁ : GInf E s → ℂ} {k' : Bool → GInf E s' → ℂ} {d' : Bool} (hk' : IsConjKernelPair k')
    (T : Space E m t) (e₂ : GInf E t → ℂ) (a a' : J → ∀ (n : Type) [Fintype n], AutChar E)
    (Φ : MvPolynomial (NumberField.InfinitePlace E × m × n) ℂ)
    (W : ∀ o : J, Finset (X o)) (u : ∀ o : J, X o → ℂ) (c : J → ℂ)
    (y : ∀ o : J, X o → S.Form e₁) (f : ∀ o : J, X o → S'.Form (k' d'))
    (N : ∀ o : J, X o → S.ModerateWeight T')
      (Ψ' : ∀ o : J, X o → Matrix n' m' (𝔪 o).ResidueRing → ℂ)
    (p : MvPolynomial (NumberField.InfinitePlace E × n' × m') ℂ) : Prop :=
  ∃ (Q : MvPolynomial (NumberField.InfinitePlace E × m × n) ℂ)
    (Ψ : ∀ o : J, X o → Matrix m n (𝔪 o).ResidueRing → ℂ) (M : ∀ o : J, X o → S'.ModerateWeight T),
    -- (a) the `u`-weighted sums of the periods of the lifts to `T` are proportional to `c`
    (∀ r : GInf E t, ∃ β : ℂ, ∀ o : J,
      ∑ i ∈ W o, u o i *
          periodPairing hk' (M o i) r (f o i) (modLift S T (a o) Φ (Ψ o i) e₁ e₂ (y o i)) =
        β * c o) ∧
    -- (b) the two kernels agree up to the weights
    ∀ (o : J) (i : X o) (g : G E s) (x : G E s'),
      (N o i).weightFn g *
          modKernel T' S' (a' o m') (a' o n') (𝔪 o) (Ψ' o i) p ((N o i).comparisonMap g) x =
        (M o i).weightFn x *
          modKernel S T (a o n) (a o m) (𝔪 o) (Ψ o i) Q g ((M o i).comparisonMap x)

/-- Seesaw, for families indexed by `o : J` and `i : X o`. Take two edge families
(`New.Exchange.IsEdgeFamily`): characters `a` with polynomial `Φ` for `S → T`, and characters `a'`
with polynomial `Φ'` for `T' → S'`. Take forms `y o i` on `S` and `f o i` on `S'`, moderate weights
`N o i`, and finite data `Ψ' o i` on matrices over residue rings. Suppose the matched polynomials
(`New.Exchange.IsSeesawMatched`) span all polynomials. These are the ones whose kernel agrees, up to
moderate weights, with a kernel of `S → T` for some polynomial and finite data `Ψ`, such that the
`u`-weighted sums over `W o` of the periods of `f` against the real translates of the lifts of `y`
by `Φ` and `Ψ` are multiples of `c`. Then there is a single `β` such that, for every `o`, the sum
over `i ∈ W o` of `u o i` times the period (`New.Space.periodPairing`, with weight `N o i`, moved by
`r`) of `y o i` against the transposed lift `modTransposedLift` of `f o i` equals `β * c o`. -/
lemma Exchange.seesaw_periods (J : Type*) {X : J → Type}
    {a a' : J → ∀ (n : Type) [Fintype n], AutChar E} {𝔪 : J → Modulus E} {W : ∀ o : J, Finset (X o)}
    {c : J → ℂ} {k : Bool → GInf E s → ℂ} {l : Bool → GInf E t → ℂ} {k' : Bool → GInf E s' → ℂ}
    {l' : Bool → GInf E t' → ℂ} {d d' : Bool}
    {Φ : MvPolynomial (NumberField.InfinitePlace E × m × n) ℂ}
    {Φ' : MvPolynomial (NumberField.InfinitePlace E × n' × m') ℂ} {r : GInf E t'}
    {u : ∀ o : J, X o → ℂ} {y : ∀ o : J, X o → S.Form (k d)} {f : ∀ o : J, X o → S'.Form (k' !d')}
    {N : ∀ o : J, X o → S.ModerateWeight T'}
      {Ψ' : ∀ o : J, X o → Matrix n' m' (𝔪 o).ResidueRing → ℂ}
    (h_edge : IsEdgeFamily a k l d Φ) (h_edge' : IsEdgeFamily a' l' k' d' Φ')
    (h_span : ⊤ ≤ span ℂ {p : MvPolynomial (NumberField.InfinitePlace E × n' × m') ℂ |
      IsSeesawMatched h_edge'.isConjKernelPair_target T (l d) a a' Φ W u c y f N Ψ' p}) :
    ∃ β : ℂ, ∀ o : J,
      ∑ i ∈ W o, u o i *
          periodPairing h_edge.isConjKernelPair_source (N o i) r (y o i)
            (modTransposedLift T' S' (a' o) Φ' (Ψ' o i) (k' !d') (l' !d') (f o i)) =
        β * c o := by
  -- For a Fock vector `v` let `L v o` be the `u o`-weighted sum over `W o` of the double integrals
  -- of the kernel of `T' → S'` against `N * y` and `f`. The family `L v` is continuous in `v`, lies
  -- on the line `ℂ ∙ c` for the matched polynomials (see-saw and Fubini), hence for all `v`; the
  -- claim is the case of a translate of `Φ'`. The characters `a'` have weights `γ`, `γ'` that do
  -- not depend on `o`.
  obtain ⟨-, hk', γ, γ', ψ, hγ, hγ', -⟩ := id h_edge'
  have hk : IsConjKernelPair k := h_edge.isConjKernelPair_source
  have h_functional (o : J) (i : X o) :
      ∃ Λ : fockSpace (realSigns E (homSigns t' s')) →L[ℂ] ℂ,
        ∀ v : fockSpace (realSigns E (homSigns t' s')),
          Λ v = ∫ g : G E s, ∫ x : G E s', (N o i).weightFn g * y o i g *
              ((T'.hom S').θ (pairWeil T' S' (a' o m') (a' o n') ((N o i).comparisonMap g, x)
                (modDatum T' S' (𝔪 o) (Ψ' o i) v)) * f o i x) ∂S'.quotMeasure ∂S.quotMeasure :=
    exists_continuousLinearMap_eq_integral_kernel_mul_forms hk hk' (a' o m') (a' o n') (Ψ' o i)
      (N o i) (y o i) (f o i)
  choose Lᵢ hLᵢ using h_functional
  let L : fockSpace (realSigns E (homSigns t' s')) →L[ℂ] J → ℂ :=
    .pi fun o ↦ ∑ i ∈ W o, u o i • Lᵢ o i
  have L_apply (v : fockSpace (realSigns E (homSigns t' s'))) (o : J) :
      L v o = ∑ i ∈ W o, u o i * Lᵢ o i v := by simp [L]
  have h_line (v : fockSpace (realSigns E (homSigns t' s'))) : L v ∈ ℂ ∙ c := by
    -- The preimage of the line is closed and polynomials are dense; matched ones span them.
    refine denseRange_polyVector.induction_on v
      ((closed_of_finiteDimensional _).preimage L.continuous) fun p ↦
        (span_le (p := (ℂ ∙ c).comap (L.toLinearMap ∘ₗ polyVector _))).2 ?_ (h_span mem_top)
    rintro p ⟨Q, Ψ, M, h_period, h_kernel⟩
    let U (o : J) (i : X o) : T.Form (l d) := modLift S T (a o) Φ (Ψ o i) (k d) (l d) (y o i)
    -- `P o i r` is the period of `f o i` against the lift `U o i` moved by `r`
    let P (o : J) (i : X o) (r : GInf E t) : ℂ := periodPairing hk' (M o i) r (f o i) (U o i)
    choose β hβ using show ∀ r, ∃ β : ℂ, ∀ o, ∑ i ∈ W o, u o i * P o i r = β * c o from h_period
    -- the lift with datum `Q` is the average against `α` of real translates of that with `Φ`
    obtain ⟨α, h_avg⟩ : ∃ α : CompactlySupportedContinuousMap (GInf E t) ℂ, ∀ (o : J) (i : X o),
        lift (pairThetaKer S T (a o n) (a o m))
            (modDatum S T (𝔪 o) (Ψ o i) (polyVector (realSigns E (homSigns s t)) Q)) (y o i) =
          realConv α (U o i) :=
      (h_edge.exists_lift_eq_realConv Q).imp fun α hα o i ↦ hα o S T (𝔪 o) (Ψ o i) (y o i)
    have h_int (o : J) (i : X o) : Integrable fun r : GInf E t ↦ α r * P o i r := by
      simpa [P, periodPairing, integral_const_mul] using
        (integrable_mul_weight_mul_forms hk' α (M o i) (f o i) (U o i)).integral_prod_left
    -- the see-saw: each double integral in `L` is the `α`-average of the periods of the lift
    have h_seesaw (o : J) (i : X o) : Lᵢ o i (polyVector _ p) = ∫ r, α r * P o i r :=
      (hLᵢ o i _).trans <| integral_kernel_mul_forms_eq_integral_periodPairing hk hk' (f o i)
        (h_avg o i) (h_kernel o i)
    -- average `hβ` against `α` and exchange the finite sum with the integral over `r`
    refine mem_span_singleton.2 ⟨∫ r, α r * β r, funext fun o ↦ ?_⟩
    calc (∫ r, α r * β r) * c o = ∫ r, ∑ i ∈ W o, u o i * (α r * P o i r) := by
          simp_rw [← integral_mul_const, mul_assoc, ← hβ, Finset.mul_sum, mul_left_comm _ (u ..)]
      _ = L (polyVector _ p) o := by
          rw [L_apply, integral_finsetSum _ fun i _ ↦ (h_int o i).const_mul _]
          simp_rw [integral_const_mul, h_seesaw]
  -- The transposed lift is the integral of the kernel against `f` (`coe_formLift`); translating it
  -- by `r` moves the datum (`lift_mul_right`), and only its real part (`pairWeil_integrated`, by
  -- the weights `hγ`, `hγ'`).
  have h_descent (o : J) (i : X o) :
      periodPairing hk (N o i) r (y o i)
          (modTransposedLift T' S' (a' o) Φ' (Ψ' o i) (k' !d') (l' !d') (f o i)) =
        Lᵢ o i (realPairWeil γ γ' (r, 1) (polyVector _ Φ')) := by
    have h_translate (g : G E t') :
        (modTransposedLift T' S' (a' o) Φ' (Ψ' o i) (k' !d') (l' !d') (f o i)).val (g * (r, 1)) =
          ∫ x : G E s', (T'.hom S').θ (pairWeil T' S' (a' o m') (a' o n') (g, x)
            (modDatum T' S' (𝔪 o) (Ψ' o i) (realPairWeil γ γ' (r, 1) (polyVector _ Φ')))) *
              f o i x ∂S'.quotMeasure := by
      rw [(h_edge'.isArrow_swap T' S' (Ψ' o i) o).coe_formLift, lift_mul_right]
      simp [lift, modDatum, ← Prod.mk_one_one, pairWeil_integrated]
    simp only [hLᵢ, periodPairing, LinearMap.mk₂_apply, h_translate, integral_const_mul]
  obtain ⟨β, hβ⟩ := mem_span_singleton.1 (h_line (realPairWeil γ γ' (r, 1) (polyVector _ Φ')))
  refine ⟨β, fun o ↦ ?_⟩
  simp_rw [h_descent, ← L_apply, ← hβ, Pi.smul_apply, smul_eq_mul]

end New

end
