import New.UpperBound.Seesaw.NeighbourLattice

/-!
# The vacuum of the neighbour lattice

The sum of the translates of the vacuum by the representatives of the neighbour lattice is computed
on the two edges of the pair. A representative is `neighbourTranslation X X'' y + t`, for residues
`y` and a vector `t` that vanishes above `N`. The translations by the `neighbourTranslation X X'' y`
add up to `doubleLiftGluing`, and they commute with the translations that vanish above `N`. So a
translate of the sum by such a vector is a sum of roots of unity times vectors `gluedTranslate`,
one for each class of the `t`. The result is
`isAdmissibleCombination_finHeisenbergOp_sum_neighbourCosetRep`.

Notions from other files:
* `PairIndex X X''`: the indices of a basis of `X⁻ ⊕ X''`, where each of the two definite spaces
  has a last basis vector.
* `neighbourTranslation X X'' y`: the matrix attached to residues `y` modulo `N` at the places of
  `P`, with `η ȳ / N` (`η` the unit of norm `-1`) in the row of the last basis vector of `X`,
  `-ȳ / N` in that of `X''`, and zero elsewhere. It is supported at the places conjugate to `P`.
* `vanishingAbove ι P`: the vectors that vanish at the places of `P` and their conjugates (for
  split `N`, the places above `N`).
* `AwayLatticeQuotient`, `neighbourCosetRep`: the classes, modulo the integral ones, of the
  elements of the neighbour lattice that vanish above `N`, and the sum
  `neighbourTranslation X X'' y + t` for a chosen representative `t` of such a class.
* `Z.finHeisenbergOp x`, `Z.vacElem`: the translation by a finite adelic vector `x` and the vacuum
  in the space `𝒮 Z`.
* `IsAdmissibleCombination v A n d p B z`: `z` is a finite combination of the `v x` with `x ∈ A`,
  whose coefficients times `d` are integral away from `n` and, if `p` holds, have absolute sum at
  most `B` under every automorphism of `ℂ`.
* `arrowTensor`: the map that joins data on `Hom(V, V')` and `Hom(V', V'')` to one datum on
  `Hom(V', V⁻ ⊕ V'')`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

namespace New.Seesaw

noncomputable section

open Matrix Space WeilData Exchange Finset Weil Valued Splitting stdLattice DoubleLiftData
  TensorProduct
  PairIndex

section Translations

variable {E X X' X'' : Type} [Field E] [CMType E] [WeilData E] [Fintype X] [DecidableEq X]
  [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X''] {N : ℕ} {P : Finset (FinPlace E)}
  {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E} {κ : PairIndex X X'' → 𝔸f E}

variable (E X X' X'') in
/-- The space `Hom (X', (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))` of the standard spaces, the target of
`arrowTensor` for a pair of standard edges. -/
abbrev stdPairSpace : Space E (PairIndex X X'' × X') (homSigns 1 (-1 ⊕ᵥ 1)) :=
  (stdSpace E X').hom (flipSum (stdSpace E (X ⊕ Unit)) (stdSpace E (X'' ⊕ Unit)))

/-- The glued translate attached to a pair of finite adelic matrices `t = (t₁, t₂)`: translate the
vacuum of the edge `Hom(X ⊕ Unit, X')` by `t₁` and that of `Hom(X', X'' ⊕ Unit)` by `t₂`, and apply
`doubleLiftGluing` (the sum over residues modulo `N` at `P`) to the tensor of the two. -/
def gluedTranslate (N : ℕ) [Fact N.Prime] (P : Finset (FinPlace E))
    (t : (X' × (X ⊕ Unit) → 𝔸f E) × ((X'' ⊕ Unit) × X' → 𝔸f E)) :
    ((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).finitePart ⊗[ℂ]
      ((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).finitePart :=
  doubleLiftGluing X X' P N X''
    (((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).heisenbergFinPart t.1
        ⟨((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).vacElem, vacElem_mem_finitePart⟩ ⊗ₜ
      ((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).heisenbergFinPart t.2
        ⟨((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).vacElem, vacElem_mem_finitePart⟩)

/-- There is a constant `C` such that, for every `n` prime to `N` and every proposition `p`, the map
`L` sends each translate of the vacuum of `Hom(V', V⁻ ⊕ V'')` by a matrix `y`, whose row `i` times
`d i` is integral away from `n`, to an admissible combination of the vectors
`C • gluedTranslate N P (t₁, t₂)`, where `β̄ t₁`, `β̄ t₂` are integral away from `n`. The
coefficients are integral away from `n` after multiplication by the number of classes of integral
matrices modulo `β`, and if `p` holds their absolute sum is at most `1` under every automorphism
of `ℂ`. -/
def IsAdmissibleEval {ι ι' ι'' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    [Fintype ι''] [DecidableEq ι''] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {V : Space E ι ε}
    {V' : Space E ι' ε'} {V'' : Space E ι'' ε''} (N : ℕ) [Fact N.Prime] (P : Finset (FinPlace E))
    (β : Ô E) (L : 𝒮 (V'.hom (flipSum V V'')) →
      ((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).finitePart ⊗[ℂ]
        ((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).finitePart)
    (d : ι ⊕ ι'' → 𝔸f E) : Prop :=
  ∃ C : ℂ, ∀ (n : ℕ) (p : Prop), N.Coprime n →
    ∀ y ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ d i.1,
      IsAdmissibleCombination
        (fun t : (X' × (X ⊕ Unit) → 𝔸f E) × ((X'' ⊕ Unit) × X' → 𝔸f E) ↦
          C • gluedTranslate N P t)
        (translations (X' × (X ⊕ Unit)) n (star (β : 𝔸f E)) ×ˢ
          translations ((X'' ⊕ Unit) × X') n (star (β : 𝔸f E))) n
        (Nat.card (PairIndex X X'' × X' → Ô E ⧸ Ideal.span {β})) p 1
        (L ((V'.hom (flipSum V V'')).finHeisenbergOp y (V'.hom (flipSum V V'')).vacElem))

/-! ### Translations above `N` and away from `N` -/

/-- Let `N = π π̄` with no place of `P` conjugate to one in `P` (`hπ`). A vector `x` fixed by
multiplication by the conjugate of `idem P` (the adele with component `1` on `P` and `0` elsewhere)
is supported at the places conjugate to `P`, so `x* x = 0`. Hence `semichar x`, an additive
character of a multiple of `x* x`, is `1`. -/
lemma semichar_eq_one_of_smul_eq (hπ : IsSplitSquarefree P (N : E) π) {ι : Type} [Fintype ι]
    {x : ι → 𝔸f E} (hx : star (idem P : 𝔸f E) • x = x) : semichar x = 1 := by
  apply semichar_eq_one_of_dotProduct_self_eq_zero
  rw [← hx, star_smul, star_star, smul_dotProduct, dotProduct_smul, smul_smul,
    idem_mul_star hπ.isConjDisjoint, zero_smul]

section Commute

variable [Fact N.Prime] {s : PairIndex X X'' × X' → ℤˣ} (Z : Space E (PairIndex X X'' × X') s)
  {x : PairIndex X X'' × X' → 𝔸f E}

omit [DecidableEq X] [DecidableEq X'] [DecidableEq X''] in
/-- Let `N = π π̄` with `π` a uniformiser at the places of `P`, none conjugate to another, and a
unit elsewhere (`hπ`). The matrix `neighbourTranslation X X'' y`, whose only nonzero rows are
multiples of `ȳ / N` at the two last basis vectors and which is supported at the places conjugate
to `P`, is orthogonal to every matrix `x` that vanishes at the places of `P` and their
conjugates. -/
lemma star_neighbourTranslation_dotProduct_eq_zero (hπ : IsSplitSquarefree P (N : E) π)
    (y : X' → P → ZMod N) (hx : x ∈ vanishingAbove (PairIndex X X'' × X') P) :
    star (neighbourTranslation X X'' y) ⬝ᵥ x = 0 := by
  rw [← idem_conjClosure_smul_neighbourTranslation hπ, star_smul, star_idem_conjClosure,
    smul_dotProduct,
    ← dotProduct_smul, mem_vanishingAbove.1 hx, dotProduct_zero]

/-- Let `N = π π̄` with `π` a uniformiser at the places of `P`, none conjugate to another, and a
unit elsewhere (`hπ`). The matrix `neighbourTranslation X X'' y`, made from residues `y` modulo
`N`, is supported at the conjugates of these places. So if `x` vanishes at the places of `P` and
their conjugates, the translation of `f ∈ 𝒮 Z` by `neighbourTranslation X X'' y + x` is the
product of the translations by the two summands. -/
lemma finHeisenbergOp_neighbourTranslation_add (hπ : IsSplitSquarefree P (N : E) π)
    (y : X' → P → ZMod N) (hx : x ∈ vanishingAbove (PairIndex X X'' × X') P) (f : 𝒮 Z) :
    Z.finHeisenbergOp (neighbourTranslation X X'' y + x) f =
      Z.finHeisenbergOp (neighbourTranslation X X'' y) (Z.finHeisenbergOp x f) := by
  rw [finHeisenbergOp_finHeisenbergOp, star_dotProduct,
    star_neighbourTranslation_dotProduct_eq_zero hπ y hx, star_zero, mul_zero,
    AddChar.map_zero_eq_one, one_smul]

/-- Let `N = π π̄` with `π` a uniformiser at the places of `P`, none conjugate to another, and a
unit elsewhere (`hπ`). The matrix `neighbourTranslation X X'' y`, made from residues `y` modulo
`N`, is supported at the conjugates of these places. So the translation of `𝒮 Z` by it commutes
with the translation by any `x` that vanishes at the places of `P` and their conjugates. -/
lemma finHeisenbergOp_comm_neighbourTranslation (hπ : IsSplitSquarefree P (N : E) π)
    (y : X' → P → ZMod N) (hx : x ∈ vanishingAbove (PairIndex X X'' × X') P) (f : 𝒮 Z) :
    Z.finHeisenbergOp x (Z.finHeisenbergOp (neighbourTranslation X X'' y) f) =
      Z.finHeisenbergOp (neighbourTranslation X X'' y) (Z.finHeisenbergOp x f) := by
  rw [finHeisenbergOp_comm, star_neighbourTranslation_dotProduct_eq_zero hπ y hx,
    AddChar.map_zero_eq_one, one_smul]

end Commute

omit [WeilData E] [Fintype X] [DecidableEq X] [Fintype X''] [DecidableEq X''] in
/-- If the scaling data `β`, `δ`, `κ` are away from `N` (`hκ`), then `β` is a unit above `N`, hence
so are `β̄` and every denominator `selfOrConj β b` (`β` on the first block, `β̄` on the second). -/
lemma v_selfOrConj_eq_one (hκ : IsScalingAtM N β δ κ) {ι ι' : Type} (b : ι ⊕ ι') {w : FinPlace E}
    (hw : ↑N ∈ w.asIdeal) : v (selfOrConj β b w) = 1 := by
  rw [selfOrConj]
  split_ifs
  exacts [hκ.v_eq_one w hw, (v_star_apply ..).trans (hκ.v_eq_one (star w) (by simpa using hw))]

omit [Fintype X] [DecidableEq X] [Fintype X''] [DecidableEq X''] in
/-- Let `P` contain one place of each conjugate pair above the prime `N`, let `β` be a unit above
`N` and `n` prime to `N`. Let `W` be a hermitian space on the entries of a matrix with two blocks of
rows. If the rows of `y` have denominator at most `β` in the first block and `β̄` in the second
(`selfOrConj β`) away from `n`, the translate of the vacuum of `W` by `y` is a root of unity times
the translate by a matrix `y'` that has the same denominators and vanishes above `N`. -/
lemma exists_finHeisenbergOp_vacElem_eq_of_coprime (hP : IsSplitLevel P N)
    (hκ : IsScalingAtM N β δ κ)
    {ι ι' ι'' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι'']
    [DecidableEq ι''] {s : (ι ⊕ ι'') × ι' → ℤˣ} (W : Space E ((ι ⊕ ι'') × ι') s) {n : ℕ}
    (hn : N.Coprime n) {y : (ι ⊕ ι'') × ι' → 𝔸f E}
    (hy : y ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1) :
    ∃ ζ : ℂ, IsOfFinOrder ζ ∧
      ∃ y' ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1,
        y' ∈ vanishingAbove ((ι ⊕ ι'') × ι') P ∧
          W.finHeisenbergOp y W.vacElem = ζ • W.finHeisenbergOp y' W.vacElem := by
  -- The part `l` of `y` above `N` is integral; take `y' = y - l`.
  let l : (ι ⊕ ι'') × ι' → 𝔸f E := (idem (P : Set (FinPlace E)).conjClosure : 𝔸f E) • y
  have hl : l ∈ stdLattice E ((ι ⊕ ι'') × ι') := by
    refine fun i ↦ idem_mul_mem_Ô.2 fun w hw ↦ ?_
    have hN : ↑N ∈ w.asIdeal := by simpa [hP.natCast_mem_iff] using hw
    have h_le : v ((selfOrConj β i.1 * y i) w) ≤ 1 :=
      hy i w (w.isPrime.notMem_of_isCoprime_of_mem hn.cast hN)
    simpa [v_selfOrConj_eq_one hκ i.1 hN] using h_le
  have hl_den : l ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1 := by
    intro i w _
    have h_den : selfOrConj β i.1 ∈ Ô E := ite_mem.2 ⟨fun _ ↦ β.2, fun _ ↦ star_mem_Ô β.2⟩
    exact mem_Ô.1 (mul_mem h_den (hl i)) w
  obtain ⟨ζ, hζ, h_shift⟩ := exists_finHeisenbergOp_add_vacElem W y (neg_mem hl)
  rw [← sub_eq_add_neg] at h_shift
  exact ⟨ζ, hζ, y - l, sub_mem hy hl_den, sub_idem_smul_mem_vanishingAbove y, h_shift⟩

end Translations

/-! ### The two edges of the pair -/

section Edges

variable {E : Type} [Field E] [CMType E] [WeilData E] {ι ι' ι'' : Type} [Fintype ι]
  [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι'']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ}
  {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''}

/-- On a pure tensor `Φ ⊗ Ψ` of data on the two edges, `arrowTensor` is `arrowProduct Φ Ψ`. -/
lemma arrowTensor_tmul (Φ : (V.hom V').finitePart) (Ψ : (V'.hom V'').finitePart) :
    arrowTensor (Φ ⊗ₜ[ℂ] Ψ) = arrowProduct (Φ : 𝒮 (V.hom V')) (Ψ : 𝒮 (V'.hom V'')) :=
  rfl

/-- The translate by `z` of the vacuum of `Hom(V', V⁻ ⊕ V'')` is the square of `semichar` of the
first block of `z` times the image under `arrowTensor` of the tensor of two translates. These are
the vacuum of `Hom(V, V')` translated by `normNegOne` (the unit of norm `-1`) times the adjoint of
the first block of `z`, and the vacuum of `Hom(V', V'')` translated by the second block of `z`. -/
lemma finHeisenbergOp_vacElem_eq_smul_arrowTensor (z : (ι ⊕ ι'') × ι' → 𝔸f E) :
    (V'.hom (flipSum V V'')).finHeisenbergOp z (V'.hom (flipSum V V'')).vacElem =
      semichar (fun i : ι' × ι ↦ z (Sum.inl i.2, i.1)) ^ 2 • arrowTensor
        ((V.hom V').heisenbergFinPart
            (fun i : ι' × ι ↦ (normNegOne (E := E) : 𝔸f E) * star (z (Sum.inl i.2, i.1)))
            ⟨(V.hom V').vacElem, vacElem_mem_finitePart⟩ ⊗ₜ[ℂ]
          (V'.hom V'').heisenbergFinPart (fun i : ι'' × ι' ↦ z (Sum.inr i.1, i.2))
            ⟨(V'.hom V'').vacElem, vacElem_mem_finitePart⟩) := by
  rw [arrowTensor_tmul, heisenbergFinPart_apply_coe, heisenbergFinPart_apply_coe,
    ← arrowProduct_vacElem, finHeisenbergOp_arrowProduct]

end Edges

/-! ### The sum over the neighbour lattice -/

section Sum

variable {E X X' X'' : Type} [Field E] [CMType E] [WeilData E] [Fintype X] [DecidableEq X]
  [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X''] {N : ℕ} [Fact N.Prime]
  {P : Finset (FinPlace E)} {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E} {κ : PairIndex X X'' → 𝔸f E}

open scoped Classical in
/-- Let `N` be a prime that splits as `N = π π̄`. Let `t` be a tensor of finite data (`finitePart`)
on the two edges `Hom(X ⊕ Unit, X')` and `Hom(X', X'' ⊕ Unit)` of standard spaces. The map
`arrowTensor` joins it to one datum on `stdPairSpace`, the space
`Hom(X', (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))`. There the operator `doubleLiftGluing` (the sum over residues
`y` of the translation of the first datum by the last column `-y / N` and of the second by the last
row `-ȳ / N`) becomes the sum of the translations by `neighbourTranslation X X'' y`, the matrices
whose only nonzero rows are `η ȳ / N` and `-ȳ / N` at the two last basis vectors. -/
lemma arrowTensor_doubleLiftGluing (hπ : IsSplitSquarefree P (N : E) π)
    (t : ((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).finitePart ⊗[ℂ]
      ((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).finitePart) :
    arrowTensor (doubleLiftGluing X X' P N X'' t) =
      ∑ y : X' → P → ZMod N,
        (stdPairSpace E X X' X'').finHeisenbergOp (neighbourTranslation X X'' y)
          (arrowTensor t) := by
  induction t with
  | add t t' ht ht' => simp [ht, ht', Finset.sum_add_distrib]
  | tmul Φ Ψ =>
    -- The adjoint, times the unit of norm `-1`, turns the first nonzero row of
    -- `neighbourTranslation y` into the last column `-y / N`; the second nonzero row is the last
    -- row `-ȳ / N`.
    have h_column (y : X' → P → ZMod N) :
        (fun q : X' × (X ⊕ Unit) ↦ (normNegOne (E := E) : 𝔸f E) *
          star (neighbourTranslation X X'' y (Sum.inl q.2, q.1))) = poleColumn X y := by
      ext ⟨a, i | i⟩ : 1 <;> simp [neighbourTranslation, ← mul_assoc, mul_comm _ (star _)]
    have h_row (y : X' → P → ZMod N) :
        (fun q : (X'' ⊕ Unit) × X' ↦ neighbourTranslation X X'' y (Sum.inr q.1, q.2)) =
          poleRow X'' y := by
      ext ⟨i | i, a⟩ : 1 <;> simp [neighbourTranslation]
    have h_phase (y : X' → P → ZMod N) :
        semichar (fun q : X' × (X ⊕ Unit) ↦ neighbourTranslation X X'' y (Sum.inl q.2, q.1)) = 1 :=
      semichar_eq_one_of_smul_eq hπ <|
        funext fun q ↦ congrFun (star_idem_smul_neighbourTranslation y) (Sum.inl q.2, q.1)
    simp only [doubleLiftGluing, LinearMap.sum_apply, map_sum, map_tmul, arrowTensor_tmul,
      finHeisenbergOp_arrowProduct, h_column, h_row, h_phase, one_pow, one_smul,
      heisenbergFinPart_apply_coe]

open scoped Classical in
/-- Let `N` be a prime that splits as `N = π π̄`, where `π` is a uniformiser at the places of `P`
and a unit elsewhere. Let `z` be a matrix on `PairIndex X X''` times `X'` whose rows have
denominator at most `β` in the first block and `β̄` in the second (`selfOrConj β`), away from `n`.
In `stdPairSpace`, the space `Hom(X', (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))`, add up over residues `y` modulo
`N` at `P` the translates, by `neighbourTranslation X X'' y`, of the translate of the vacuum by `z`.
The sum is a root of unity times the image under `arrowTensor` of `gluedTranslate N P (t₁, t₂)`, the
glued tensor of the translates by `t₁`, `t₂` of the vacua of the two edges, for some `t₁`, `t₂` with
`β̄ t₁`, `β̄ t₂` integral away from `n`. -/
lemma exists_sum_finHeisenbergOp_neighbourTranslation_eq (hπ : IsSplitSquarefree P (N : E) π)
    {n : ℕ} {z : PairIndex X X'' × X' → 𝔸f E}
    (hz : z ∈ weightedTranslations n fun i : PairIndex X X'' × X' ↦ selfOrConj β i.1) :
    ∃ ζ : ℂ, IsOfFinOrder ζ ∧
      ∃ t₁ ∈ translations (X' × (X ⊕ Unit)) n (star (β : 𝔸f E)),
        ∃ t₂ ∈ translations ((X'' ⊕ Unit) × X') n (star (β : 𝔸f E)),
          ∑ y : X' → P → ZMod N, (stdPairSpace E X X' X'').finHeisenbergOp
            (neighbourTranslation X X'' y)
              ((stdPairSpace E X X' X'').finHeisenbergOp z (stdPairSpace E X X' X'').vacElem) =
            ζ • arrowTensor (gluedTranslate N P (t₁, t₂)) := by
  -- `z` splits into `t₁` on the first edge, through the adjoint, and `t₂` on the second.
  let t₁ : X' × (X ⊕ Unit) → 𝔸f E := fun i ↦
    (normNegOne (E := E) : 𝔸f E) * star (z (Sum.inl i.2, i.1))
  have ht₁ : t₁ ∈ translations (X' × (X ⊕ Unit)) n (star (β : 𝔸f E)) :=
    star_mem_weightedTranslations normNegOne_mem hz fun i : X' × (X ⊕ Unit) ↦ (Sum.inl i.2, i.1)
  let t₂ : (X'' ⊕ Unit) × X' → 𝔸f E := fun i ↦ z (Sum.inr i.1, i.2)
  have ht₂ : t₂ ∈ translations ((X'' ⊕ Unit) × X') n (star (β : 𝔸f E)) := fun i ↦
    hz (Sum.inr i.1, i.2)
  refine ⟨semichar (fun i : X' × (X ⊕ Unit) ↦ z (Sum.inl i.2, i.1)) ^ 2, (isOfFinOrder_ψf _).pow,
    t₁, ht₁, t₂, ht₂, ?_⟩
  simp only [t₁, t₂, finHeisenbergOp_vacElem_eq_smul_arrowTensor, gluedTranslate,
    arrowTensor_doubleLiftGluing hπ, map_smul, smul_sum]

open scoped Classical in
/-- Let `N = π π̄` be a split prime with places `P`. By `hκ`, `β` is a unit above `N` and each row
factor `κ` is `1` or `δ`, with denominator at most `β̄`. The classes
`q : AwayLatticeQuotient X' hπ hκ` are those, modulo integral matrices, of the elements of the
neighbour lattice that vanish above `N`; for residues `y` modulo `N` at `P`,
`neighbourCosetRep (y, q)` is `neighbourTranslation X X'' y` plus a chosen representative of `q`.

Let `x` vanish above `N` and have rows of denominator at most `β` in the first block and `β̄` in the
second, away from `n`. Translate by `x` the sum over `(y, q)` of the translates of the vacuum by
these representatives, and read the result on the two edges `Hom(X ⊕ Unit, X')`,
`Hom(X', X'' ⊕ Unit)`. With `K` the number of classes `q`, it is a finite combination of
`K • gluedTranslate N P (t₁, t₂)`, where `gluedTranslate` glues the translates by `t₁`, `t₂` of the
vacua of the edges and `β̄ t₁`, `β̄ t₂` are integral away from `n`. Its coefficients, times the
number of integral matrices modulo `β`, are integral away from `n`. The proposition `boundHyp` is
arbitrary; if it holds, the absolute sum of the coefficients is at most `1` under every automorphism
of `ℂ`. -/
theorem isAdmissibleCombination_finHeisenbergOp_sum_neighbourCosetRep
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) {n : ℕ} (boundHyp : Prop)
    {x : PairIndex X X'' × X' → 𝔸f E}
    (hx : x ∈ weightedTranslations n fun i : PairIndex X X'' × X' ↦ selfOrConj β i.1)
    (hx_zero : x ∈ vanishingAbove (PairIndex X X'' × X') P) :
    IsAdmissibleCombination
      (fun t : (X' × (X ⊕ Unit) → 𝔸f E) × ((X'' ⊕ Unit) × X' → 𝔸f E) ↦
        (Fintype.card (AwayLatticeQuotient X' hπ hκ) : ℂ) • gluedTranslate N P t)
      (translations (X' × (X ⊕ Unit)) n (star (β : 𝔸f E)) ×ˢ
        translations ((X'' ⊕ Unit) × X') n (star (β : 𝔸f E))) n
      (Nat.card (PairIndex X X'' × X' → Ô E ⧸ Ideal.span {β})) boundHyp 1
      (arrowTensor.leftInverse ((stdPairSpace E X X' X'').finHeisenbergOp x
        (∑ a : (X' → P → ZMod N) × AwayLatticeQuotient X' hπ hκ,
          (stdPairSpace E X X' X'').finHeisenbergOp (neighbourCosetRep a)
            (stdPairSpace E X X' X'').vacElem))) := by
  let Z := stdPairSpace E X X' X''
  let K : ℕ := Fintype.card (AwayLatticeQuotient X' hπ hκ)
  -- The term of a class `q`: its representative splits off, and `x` passes the shifts.
  let classTerm (q : AwayLatticeQuotient X' hπ hκ) : 𝒮 Z := ∑ y : X' → P → ZMod N,
    Z.finHeisenbergOp (neighbourTranslation X X'' y)
      (Z.finHeisenbergOp x (Z.finHeisenbergOp q.out.val Z.vacElem))
  have h_terms : Z.finHeisenbergOp x (∑ a : (X' → P → ZMod N) × AwayLatticeQuotient X' hπ hκ,
      Z.finHeisenbergOp (neighbourCosetRep a) Z.vacElem) = ∑ q : AwayLatticeQuotient X' hπ hκ,
        classTerm q := by
    rw [map_sum, Fintype.sum_prod_type_right]
    refine sum_congr rfl fun q _ ↦ sum_congr rfl fun y _ ↦ ?_
    have hq_zero : q.out.val ∈ vanishingAbove (PairIndex X X'' × X') P :=
      (AddSubgroup.mem_inf.1 q.out.property).2
    rw [neighbourCosetRep, finHeisenbergOp_neighbourTranslation_add Z hπ y hq_zero,
      finHeisenbergOp_comm_neighbourTranslation Z hπ y hx_zero]
  have h_mean : arrowTensor.leftInverse (∑ q : AwayLatticeQuotient X' hπ hκ, classTerm q) =
      ∑ q : AwayLatticeQuotient X' hπ hκ,
        (1 / K : ℂ) • (K : ℂ) • arrowTensor.leftInverse (classTerm q) := by
    simp [K, smul_smul]
  have h_int : (Nat.card (PairIndex X X'' × X' → Ô E ⧸ Ideal.span {β}) : ℂ) * (1 / K) ∈
      integralAway n := by
    simpa [K, div_eq_mul_inv] using
      div_mem_integralAway ((card_awayLatticeQuotient_dvd (X' := X') hπ hκ).mul_right (n ^ 0))
  have h_size (σ : ℂ ≃+* ℂ) : ∑ _q : AwayLatticeQuotient X' hπ hκ, ‖σ (1 / K)‖ ≤ 1 := by
    simp [K]
  rw [h_terms, h_mean]
  refine (IsAdmissibleCombination.of_sum (fun _ _ ↦ h_int)
    fun _ ↦ h_size).of_eq_isOfFinOrder_smul fun q _ ↦ ?_
  -- Translations by `x` and by the representative of `q` compose to the translation by their sum
  -- up to the value `ξ` of the standard additive character `selfDualAddChar`, a root of unity.
  let ξ : ℂ := selfDualAddChar E (star traceOneAdele * star q.out.val ⬝ᵥ x)
  have h_sum_mem : x + q.out.val ∈
      weightedTranslations n fun i : PairIndex X X'' × X' ↦ selfOrConj β i.1 :=
    add_mem hx (awayLattice_le_weightedTranslations hπ hκ n q.out.property)
  obtain ⟨ζ, hζ, t₁, ht₁, t₂, ht₂, h_glue⟩ :=
    exists_sum_finHeisenbergOp_neighbourTranslation_eq hπ h_sum_mem
  have h_term : classTerm q = ξ • ζ • arrowTensor (gluedTranslate N P (t₁, t₂)) := by
    simp only [classTerm, Z, ξ, ← h_glue, smul_sum, Z.finHeisenbergOp_finHeisenbergOp (x := x),
      map_smul]
  refine ⟨ξ * ζ, (isOfFinOrder_ψf _).mul hζ, (t₁, t₂), ⟨ht₁, ht₂⟩, ?_⟩
  rw [h_term, map_smul, map_smul, leftInverse_arrowTensor, ← mul_smul ξ, smul_comm]

end Sum

end

end New.Seesaw
