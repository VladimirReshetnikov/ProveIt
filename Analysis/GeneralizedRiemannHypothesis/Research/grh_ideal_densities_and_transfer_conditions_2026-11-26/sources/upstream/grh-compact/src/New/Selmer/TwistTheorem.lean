import New.Selmer.RootsOfUnityPoints
import Lib.GaloisRep.WeightCongruence.WeightCongruence
import New.Selmer.TiltingLemma

/-! Tied conditions at new primes shrink Selmer groups. At new split primes a slope ties a cocycle's
value on tame inertia to its value at Frobenius, as the twist chosen later nearly imposes, and by
reciprocity a good prime and a generic slope shorten a long tied Selmer group, so boundedly many
primes make all these groups short. Lowering Selmer groups mod ℓ^n by new local conditions at
Chebotarev primes with trivial Frobenius is known. Related work: Fakhruddin–Khare–Patrikis, Relative
deformation theory and lifting irreducible Galois representations, 2021; Mazur–Rubin, Diophantine
stability, 2018; Darmon–Diamond–Taylor, Fermat's Last Theorem, 1995.

Part of: One anticyclotomic twist makes all Selmer groups short (see New.Selmer.TwistForRows).

This file: Boundedly many tied primes shorten Selmer groups; one anticyclotomic twist then does,
controlling L-values. -/

open Module Fintype NeZero Finset Fint
variable {ℓ} [ThePrime ℓ] {E ι : Type} [Field E] [UnramCMField E] [Finite ι] {n : ι → Type} [∀ i,
  Fintype (n i)] {S₀ S : Finset (FinPlace E)} {z M} {γ β : ι → _} (hS : S ⊆ S₀) (hz :
  z ∈ inertiaAbove (S₀ \ placesDividing E ℓ))
include hS hz
attribute [-simp] Set.insert_eq_of_mem

open IsLocalRing Ideal LinearMap Order Matrix.Module Function Ideal.Quotient in
/-- Let ρ_i over O (`PadicIntegerRing`) be balanced up to β_i, S ⊆ S₀, W a neighbourhood of z
inertial at S₀ off ℓ, a ∣ ℓ^M. For some J₀ and every N, some set of at most J₀ primes as in
`IsPencil` makes each tied Selmer module mod a, zero at γ_i, of length ≤ β_i.

Tied conditions at new primes shrink Selmer groups. -/
lemma exists_isPencil {O W} [CommRing O] [PadicIntegerRing O ℓ] {ρ : ∀ i, _ →* Matrix _ (n i) O}
  {L : ∀ _, Set _} (h : ∀ i, IsBalanced ℓ S (ρ i) (L i) (γ i) (β i) M) (hW : W ∈ nhds z) {a : O} :
  a ∣ ℓ ^ M → ∃ J₀, ∀ N, let X T J x i a := selmerModule (ρ i) (unionWithConj S T) (L i ∪
    tieRelations J x i ∪ {.single (γ i) 1}) (QuotSpan a)
  let Q := IsPencil ℓ S₀ (fun i g ↦ reduceModPow ℓ M (ρ i) g = 1) W N
  ∃ P₀ J x, Q P₀ J x ∧ #J ≤ J₀ ∧ ∀ i, length O (X J J x i a) ≤ β i := by
  refine WfDvdMonoid.induction_on_irreducible a (by simp [ne] at ·) (fun a u _ ↦
    ⟨1, (exists_isAnticyclotomicAt · ∅ S₀.finite_toSet (Subgroup.subset_normalClosure (by simpa))
    hW |>.imp fun P₀ ⟨_, _, A, _⟩ ↦ ⟨{P₀}, fun _ ↦ (A, 0), by constructor <;> simp_all [IsAuxiliary,
    isSplit_of_q_prime], by simp [(length_mono le_top).trans, u]⟩)⟩) fun a ϖ z hϖ ih ha ↦ ?_
  obtain _ := NeZero.mk z, NeZero.mk hϖ.ne_zero, dvd_of_mul_left_dvd ha
  have F i J R : Finite (selmerModule ..) := let := IsTorsionBy.module (smul_quot_eq_zero_of_dvd ha)
    have ⟨_, _, _, _, _, H⟩ :=
      exists_corepresenting_coords _ (ρ i) ((h i).1.eventually_eq 1) (finite_toSet J) R
    .of_injective _ (H _ (nsmul_quot_eq_zero ha) fun g e b ↦ congr($e • b).trans
      (by simp)).2.1.injective
  let f : {f // ker f = ⊥} := ⟨_, (span {a}).ker_liftQ_eq_bot' ((span {ϖ * a}).mkQ ∘ₗ (ϖ • 1)) (ext
    (by simp [ker_comp, mem_span_singleton, mul_dvd_mul_iff_left, ne]))⟩
  apply (ih ‹_›).imp'
  intro J₁ ih N X Q
  choose P₀ J x q d b using ih N
  have I {J x} (hp : Q P₀ J x) T ⦃k : O⦄ (hk : k ∣ ℓ ^ M) {i R K} l : selmerModule (ρ i)
    (unionWithConj S J) R (QuotSpan k) ⊓ ker (pi fun v : ↥(J \ T) ↦ evalConjPair (x v).1.γ) ≤
    selmerModule _ (unionWithConj S T) K _ := fun c ⟨a, z'⟩ ↦ selmerModule_mono
    a l fun v o ↦ have ⟨w, j, e⟩ : ∃ w ∈ J \ T, v = w ∨ v = star w := by clear * - o; grind
    (hp.3 w (sdiff_subset j) |> fun p ↦ exists_conj_side_detects (nsmul_quot_eq_zero hk) _ p.6.2.2
      p.5 (by clear * - o h; grind [inertiaAbove, IsBalanced]) e).elim fun b ⟨_, _, H⟩ ↦
    (H c a congr(($z' ⟨w, j⟩ ⟨b, ·⟩))).1
  let g (s : _ × _) k i := length O (X s.1 s.1 s.2 i k)
  obtain ⟨⟨J, x⟩, ⟨h₀, B, d⟩, W⟩ := (InvImage.wf (univ.sum <| g · (ϖ * a)) wellFounded_lt).has_min
    {t | Q P₀ t.1 t.2 ∧ g t a ≤ β ∧ #t.1 + univ.sum (g t (ϖ * a)) ≤ ?f J₁} ⟨(J, x), q, b, by
    grw [ENat.natCast_toNat, d, sum_le_sum fun i _ ↦ by grw [← relLength_add_length_inf,
      length_mono (I q ∅ ha bot_le), relLength_ker, length_mono le_top, length_top, length_pi,
      (by simpa : ENat.card _ ≤ .card (Fin J₁)), ← length_finsupp]]
    simp [length_ne_top, -length_finsupp]⟩
  refine ⟨_, _, _, h₀, Nat.cast_le.1 (le_of_add_le_left d), fun i ↦
    by_cases (h₀.length_le_of_unseen_class (h i) rfl hS ha · fun P q Z r ↦
    relLength_eq_zero.1 (not_bot_lt_iff.1 fun y ↦ ?_)) fun u ↦ (B i).trans' (length_le_of_le_map
    ((f.1.compLeft _).compLeft _) _ (mk_surjective.comp_left.comp_left.forall.2 fun s v ↦ by
    choose a e using (mem_span_singleton.1 <| hϖ.maximalIdeal_eq.le fun h ↦ u ⟨_, v, ·, ·, h.map _⟩)
    cases funext₂ e
    exact ⟨(a · ·), v.imp (fun h ↦ (comp_mem_obeying_iff .id).2 (f.2.le <|
      (comp_mem_obeying_iff _).1 h · · ·)) (.desc _ _ · (ker_eq_bot.1 f.2).comp_left), rfl⟩))⟩
  have K := by simpa [q, ker_pi, iInf_subtype] using I (r 0) J
  choose b c H using fun k [NeZero k] ↦
    tilting (evalConjPair Z.γ) (evalConjPair Z.φ) (X (insert P J) J x i k)
  obtain ⟨t, v, ht, hu⟩ := by simpa [residue_surjective.exists] using
    Cardinal.exists_notMem_of_length_lt (0 :: b (ϖ * a) ++ b a) (.trans_le (mod_cast
    (h i).5.trans_le' (by clear * - c; grind [card_prod, card_bool])) (Cardinal.natCast_toNat_le _))
  let u := (insert P J, update x P (Z, Pi.single i v.unit.inv))
  have A j k : X u.1 u.1 u.2 j k ≤ X u.1 J x .. ⊓ ker (evalConjPair Z.γ - (u.2 P).2 j • evalConjPair
    Z.φ) := fun c ↦ by simp +contextual [-Pi.single_apply, X, u, selmerModule, mem_obeying,
    funext_iff, tieRelations, evalConjPair, or_imp, forall_and, (ne_of_mem_of_not_mem · q)]
  have U {k} [NeZero k] hk h := (forall_update_iff ⊥ fun j r ↦ r + g u k j ≤ g (J, x) ..).2 ⟨by
    unfold g
    grw [length_mono, H k t h, length_mono, relLength_add_length_inf]
    grw [K hk .rfl]
    grw [A]
    simp +contextual [u, smul_smul, IsConcreteLE.le_iff],
    fun j e ↦ by simpa [bot_eq_zero'] using length_mono ((A ..).trans (by simp [u, X, *]))⟩
  have L := lt_of_le_of_lt' (by simpa [bot_eq_zero', sum_update_of_mem, X] using sum_mono (U ha
    ht)) (ENat.lt_add_left (by simp [g, length_ne_top]) y)
  exact W u ⟨r _, B.trans' (le_of_add_le_right (U ‹_› hu)), by
    grw [card_insert_le, Nat.cast_succ, add_right_comm, add_assoc, add_one_le_of_lt L, d]⟩ L

open Matrix Filter MvPolynomial ENNReal NNReal CoeffRing IsDiscreteValuationRing Subalgebra

/-- Let ρ_i be balanced up to β_i, val_k families, z inertial at S₀ off ℓ, v(μ(z) − 1) ≤ c, β_i + v
det(ρ_i z − 1) + v det(ρ_i z^{−c} − 1) ≤ B_i < ∞, η > 0. Some I, ψ make ψ^d, 1 ≤ d ≤ m, twists
(`IsAuxTwist`) raising v(val_k) by ≤ 8c + η, with ψ^dρ_i of Selmer length ≤ B_i + η.

One anticyclotomic twist makes all Selmer groups short. -/
lemma exists_anticyclotomic_twist {κ T : Type} [Finite κ] [Finite T] {O : CoeffRing ℓ} {ρ : ∀ i,
  _ →* Matrix _ (n i) O} {μ : κ → T → _} {L : ∀ _, _} {B : ι → _} (hρ : ∀ i, IsBalanced ℓ S (ρ i)
  (L i) (γ i) (β i) M) {val : κ → _} (hf : ∀ k, IsFamily S₀ (μ k) (val k)) (hB : ∀ i, B i ≠ ⊤) (hβ :
  ∀ i, O.normLength (β i + ∑ b, addVal _ (ρ i (idOrConjInv b z) - 1).det) ≤ B i) {c η : ℝ≥0} (hc :
  ∀ k t, ellVal ((μ k t z).1 - 1) ≤ c) (hη : 0 < η) m : ∃ I ψ, ∀ d ∈ Set.Icc 1 m,
  (∀ k, ellVal (val k I (ψ ^ d)) ≤ ellVal (val k ∅ 1) + 8 * c + η) ∧ IsAuxTwist S₀ I (ψ ^ d) η ∧
  ∀ i, ∀ᶠ O' in atTop, ∃ hO : O ≤ O', ∃ ψ', (∀ g, (ψ' g).1 = (ψ ^ d) g) ∧
  O'.normLength (length O' (selmerModule (twistRep (inclusion hO).1 ψ' (ρ i)) (unionWithConj S I)
  (mapRel (inclusion hO).1 '' (L i ∪ {.single (γ i) 1})) (QuotSpan (ℓ ^ M : ↑O')))) ≤ B i + η := by
  choose J₀ hJ using exists_isPencil hS hz hρ ((Eventually.all fun k ↦ .all fun t ↦
    ((IsUltrametricDist.isClosed_ball ..).preimage (Units.continuous_val.comp ((hf _).1
    _))).compl_mem_nhds (ellVal_le_iff.1 (hc k t)).not_gt).and (.all fun i ↦ (((hρ
    i).1.comp_continuous continuous_conjGal.inv).prodMk (hρ i).1).eventually_eq z)) dvd_rfl
  choose δ hδ _ using exists_pos_mul_lt hη (J₀ * 8 + 2)
  lift B ⊕ᵥ fun k ↦ ellVal (val k ∅ 1) + 8 * c to ι ⊕ κ → ℝ≥0 using by
    simp [ellVal, mul_eq_top, (hf _).4, *] with b W
  choose k hk using (exists_roots_of_unity_ellVal_le hδ 1 _ 1 _ b).exists
  choose N hN l using ((exists_roots_of_unity_ellVal_le hδ m _ _ J₀ (δ + b · + J₀ * 8 * δ)).and
    (Ici_mem_atTop _)).exists
  choose P₀ J x hp hJ hl using hJ N
  let θ (j : J) := (x j).1.h
  obtain ⟨A, o, q, a⟩ := hp.1, hp.2, J.erase_subset P₀, fun j : J ↦ hp.3 _ j.2
  have Q {y hy I} (_ : ∀ j, ↑j ∉ I → y j = (1 : PadicAlgCl ℓ) := by simp +contextual [t]) :
      IsFromU1 (placesDividing E ℓ) I (pointChar θ y hy) := by
    choose φ e b d using (a · |>.exists_ideleChar)
    use (LocallyConstant.unflip (⟨θ ·, (a _).isLocallyConstant⟩)).2.comp
      (pointChar (Pi.evalMonoidHom _) y hy), pointChar φ y hy, by simp [e], fun u h k ↦
      prod_eq_one _ fun j ↦ by by_cases j.1 ∈ I <;> simp +contextual [*], (by simp [θ, d _ · · ·])
  have U {I} : I ⊆ J → IsAuxiliary S₀ I := by clear * - A; grind
  have K {k} I (v : J) s := ((hf k).3 I v · (U s) · · _ _ (a v).3 (a v).4)
  choose O' hN hk hO hm V hV using (hN.and (hk.and (.and (Ici_mem_atTop O) (.and (.all fun p :
    (κ × T) × J × ℤˣ ↦ eventually_mem (norm_eq_one_of_continuous ((hf p.1.1).1 p.1.2) ((x
    p.2.1).1.φ ^ p.2.2.1)).le) (.all fun p : κ × Set.Iic J ↦ (
    let ⟨_, _, g, c, a, b⟩ := (hf p.1).2 _ (U p.2.2); .mono (.all (eventually_mem <| a ·)) fun O H ↦
    ⟨∑ i, C ⟨_, H i⟩ * ∏ j, X j ^ (θ j (g i)).toAdd.val, by simp [b]⟩ : ∀ᶠ O : CoeffRing ℓ in _,
    ∃ F, ∀ {y} hy, (eval y F : O.1).1 = val p.1 p.2 (pointChar θ (y ·) hy))))))).exists
  let e := (inclusion hO).1
  have r i := hp.length_le_of_drop_ties i (by simp [reduceModPow,
    (hρ i).2 · <| ·.imp fun _ ↦ by gcongr]) k l fun _ ↦ id
  let t (s : ι ⊕ κ) (j : J) := ite (↑j = P₀) 1 (s.elim (e ∘ (x j).2) 0)
  choose G g g' using fun i ↦ exists_sharp_fitting_poly (.id _) _ (a · |>.isLocallyConstant)
    (hρ i).1 (L i ∪ {.single (γ i) 1} ∪ tieRelations (J.erase P₀) x i) _
  -- First along a line.
  choose u f₃ p s using hk (Fin 1) (J × ι × Bool ⊕ _) le_rfl ((fun (v, i, b) ↦ ((ρ i (idOrConjInv b
    (x v).1.φ)⁻¹).map e).charpoly) ⊕ᵥ (.X - .C ⟨_, hm ·⟩)) (fun s ↦ eval₂ C (fun j ↦ 1 + C (t s.1 j)
    * (X 0 - 1)) (s.1.elim (.map e ∘ G) (V ⟨·, {P₀}, by simpa⟩))) 1 (by simp [↓charpoly_monic,
    Polynomial.Monic]) (by simp [↓sum_prod_type]; grw [hJ]) (by simp) (by
    rintro ⟨i | k', _⟩ <;> simp [← eval_assoc, congrFun W, hV]
    · grw [← hβ, ← hl]
      convert normLength_mono ((g i).trans (r i _ _ (one_pow _) {P₀} (idOrConjInv ·.2 z) (by simpa)
        (by simp) (by simpa using! hp.5.2 i))) <;> simp [e, eval₂_eq', eval_eq' _ (G i),
        sum_prod_type, mapRel.eq_def, twistAtPoint, funext_iff] <;> clear * - o <;> refine ?u
      ext; simp [tieRelations]; grind
    convert! K ∅ ⟨_, o⟩ (by simpa) nofun 1 ⟨.const _, 1, by simp⟩ c (by
      simpa [ellVal_le_iff, dist_eq_norm'] using hp.5.1 k')
    ext; simp)
  choose F f ϕ using fun i ↦ exists_sharp_fitting_poly e _ (a · |>.isLocallyConstant) (hρ i).1 ..
  simp [← eval_assoc, Function.comp_def] at f₃ p
  -- Then to common roots of unity.
  choose ζ f hζ w using hN J (Set.Icc 1 m) (by simpa) _ (·.1.elim F (V ⟨·, J, by simp⟩)) _
    (Polynomial.monic_X_pow_sub_C 1 <| ne_of_gt ·.2.1) (by simp [-map_one]; rfl) (fun s j ↦
    (dvd_one_add_mul_pow_sub_one (t s.1 j) p 0 .refl).1) (by
    rintro ⟨i | k', _⟩ <;> simp
    · grw (transparency := default) [← normLength_addVal, (f i).trans (r i _ e p _ _ q (by simp)
        fun _ ↦ rfl), g' i _ e, map_add, normLength_addVal, f₃.1, map_sum, sum_le_sum fun z _ ↦
        normLength_addVal _ ▸ (ellVal_le_ellVal ((dvd_iff_norm_le ..).1 ⟨det _, by
          erw [eval_charpoly, ← det_mul, sub_one_mul]; congr
          simp [← Matrix.map_mul, ← map_mul, smul_one_eq_diagonal]⟩)).trans
        (s 0 (.inl (⟨_, q z.1.2⟩, i, z.2))), ← hJ]
      simp; gcongr; norm_num
    have y j : (1 + t (.inr k') j * (u 0 - 1)).1 ^ ℓ ^ N = 1 := mod_cast l.dest.choose_spec ▸ by
      simp [pow_add, pow_mul, t, add_ite, *]
    grw [← f₃.2, hV _ y, hV _ y, ← hJ, ← q,
      ← @Finset.induction_on' _ (fun I ↦ ellVal (val k' (insert
      P₀ I) (pointChar θ _ y)) ≤ _ + #I * 8 * _) _ _ (by simp) fun v I a b w i ↦ ?_, insert_erase o]
    lift v to J using q a
    simp at a
    grw [I.insert_comm, K _ v (by grw [b]; simp [*]) (by simp [*]) _ Q δ fun z t ↦ (ellVal_le_ellVal
      ((hp.pointChar_idOrConjInv y v true).2 a ▸ by fin_cases t <;> simp [t,
      (isUnit_iff_norm_eq_one _).1 (.of_pow_eq_one p out),
      norm_eq_one_of_continuous, (hf _).1, sub_div', inv_eq_one_div, norm_pos_iff.1, norm_sub_rev,
      mul_comm (u 0).1, mul_one_div, -one_div])).trans (s 0 (.inr ((k', z), v, -t))), i]
    simp [w, add_mul, add_assoc])
  replace f s := (f s).trans (.trans_eq (coe_le_coe.2 (by linarith)) congr($W _ + η))
  have hd d j : (ζ j ^ d).1 ^ ℓ ^ N = 1 := mod_cast by simp [pow_right_comm _ d, hζ]
  use J, pointChar θ _ (hd 1), fun d e ↦ ?_
  rw [show _ ^ d = pointChar θ _ (hd d) by ext; simp [← prod_pow, pow_right_comm]]
  exact ⟨(hV .. ▸ f ⟨.inr ·, d, e⟩ :), ⟨A, Q, _, fun v ↦ ⟨(a v).5, map_one _, _, _, (a v).6.2.2⟩,
    (sum_le_card_nsmul _ _ ↑δ fun v _ ↦
    (hp.pointChar_idOrConjInv (hd d) v true).1 ▸ by simpa using w v ⟨d, e⟩).trans
    (by simp; grw [hJ]; norm_cast; bound)⟩, fun i ↦ mem_atTop_sets.2 ⟨O', fun R h ↦ ⟨hO.trans h,
    pointChar θ (inclusion h ∘ ζ ^ d) (Subtype.ext <| hd d ·), by simp, (normLength_mono
    (ϕ i _ (inclusion h).1 _)).trans (by simpa [eval₂_eq', eval_eq'] using f ⟨.inl i, d, e⟩)⟩⟩⟩
