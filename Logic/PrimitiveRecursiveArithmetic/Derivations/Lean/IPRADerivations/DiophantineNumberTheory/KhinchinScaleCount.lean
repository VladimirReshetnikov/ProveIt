import IPRADerivations.DiophantineNumberTheory.KhinchinScale
import IPRADerivations.Foundations.SumFlatten

/-!
# The active members of one Khinchin scale are the reduced fractions `𝓡_k(J)` (`hurwitz_khinchin_ipra`, (K8))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K8). With `Q' = ⌊Q/4⌋`, the
flattened activity count of `KhinchinScale` is exactly `#𝓡 = redR Q` of `KhinchinReduced`
(`scale_count`):

  `Σ_{k<(Q−⌊Q/4⌋)M} [act_k] = Σ_{⌊Q/4⌋ < q ≤ Q} #{p < M : p/q ∈ J*, gcd(p, q) = 1}`.

The flattening body `gS` is chosen so that its flattened form is literally the activity body
(`acB_eq`), so `Foundations/SumFlatten.flatten` applies directly; the rows are then identified with
`copB` (`row_pt`, `cop_pt`, and `bit_eq`: a product of bits is a bit).

Combined with `KhinchinScale.scale_measure` and `KhinchinReduced.k3_bounds` this gives (K8) for
`Q = 2^k` (`k8_bounds`): on the grid `T = R! G` (`Q ≤ R`) with `Q²w ≤ T`,

  `D Q² w ≤ 16β |E|` and `β |E| ≤ 2 D Q² w`,

i.e. `L Q² w / 32 ≤ |E| ≤ L Q² w` for `L = 2D/β` (with `w = 2r_k T`: `Lt_k/128 ≤ |E_k(J)| ≤ Lt_k/4`
after rescaling by `T`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScaleCount

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg congrEqb')
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.Foundations.IntervalAdditive (sg_of_le_one)
open LeanProofs.IPRA.Foundations.IntervalCover (measure)
open LeanProofs.IPRA.Foundations.IntervalPacking (loB hiB acB)
open LeanProofs.IPRA.Foundations.SumFlatten (flB flatten)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBad (inJT inJT_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinReduced (copB inst2_copB cqB inst2_cqB redR k3_bounds)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSeparated (actv)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScale (tup AK actK dec actC qC scale_measure)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The tail `⟨Q', T, α, γ, β⟩` of the parameter tuple. -/
abbrev tl (Q' T α γ β : PTm n) : PTm n := pairT Q' (pairT T (pairT α (pairT γ β)))

/-- The flattening body: `[act]` at `(i, p, ⟨Q', T, α, γ, β⟩)`, `q = Q' + 1 + i`. -/
def gS : PTm 3 :=
  sg (actv (var 1) (succ (fstT (var 2) + var 0)) (fstT (sndT (sndT (var 2)))) (fstT (sndT (sndT (sndT (var 2)))))
    (sndT (sndT (sndT (sndT (var 2))))))

/-- The flattened body is the activity body. -/
theorem acB_eq : acB actK = flB gS := by
  simp only [acB, actK, dec, actC, qC, flB, gS, actv, inJT, Signum.sg, gcd, PTm.subst_mul, PTm.subst_monus,
    PTm.subst_add, subst_ex2, subst_ap2, subst_eqb, Syn.subst_var, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, subst_fstT, subst_sndT]
  try rfl

theorem inst3_gS (i p x : PTm n) :
    inst3 gS i p x = sg (actv p (succ (fstT x + i)) (fstT (sndT (sndT x))) (fstT (sndT (sndT (sndT x))))
      (sndT (sndT (sndT (sndT x))))) := by
  simp only [inst3, gS, actv, inJT, Signum.sg, gcd, PTm.subst_mul, PTm.subst_monus, PTm.subst_add, subst_ex2, subst_eqb,
    Syn.subst_var, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, subst_fstT, subst_sndT]
  try rfl

/-- A row term at an explicit tail. -/
theorem row_pt (i p Q' T α γ β : PTm n) :
    Γ ⊢[PRAAx] inst3 gS i p (tl Q' T α γ β) ≐ sg (actv p (succ (Q' + i)) α γ β) := by
  rw [inst3_gS]
  have s1 : Γ ⊢[PRAAx] sndT (tl Q' T α γ β) ≐ pairT T (pairT α (pairT γ β)) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (tl Q' T α γ β)) ≐ pairT α (pairT γ β) := s1.sndE
  have s3 : Γ ⊢[PRAAx] sndT (sndT (sndT (tl Q' T α γ β))) ≐ pairT γ β := s2.sndE
  have hQ : Γ ⊢[PRAAx] fstT (tl Q' T α γ β) ≐ Q' := fst_pair _ _
  have hα : Γ ⊢[PRAAx] fstT (sndT (sndT (tl Q' T α γ β))) ≐ α := s2.fstE
  have hγ : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (tl Q' T α γ β)))) ≐ γ := s3.fstE
  have hβ : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (tl Q' T α γ β)))) ≐ β := s3.sndE
  have hq : Γ ⊢[PRAAx] succ (fstT (tl Q' T α γ β) + i) ≐ succ (Q' + i) := congrSucc (congrAdd hQ (.eqRefl _))
  exact congrSg (congrMul (inJT_congr (.eqRefl _) hq hα hγ hβ) (congrEqb' (congrGcd (.eqRefl _) hq) (.eqRefl _)))

/-- A `copB` term at an explicit parameter. -/
theorem cop_pt (p q α γ β : PTm n) :
    Γ ⊢[PRAAx] inst2 copB p (pairT q (pairT α (pairT γ β))) ≐ inJT p q α γ β * eqb (gcd p q) one := by
  rw [inst2_copB]
  have s1 : Γ ⊢[PRAAx] sndT (pairT q (pairT α (pairT γ β))) ≐ pairT α (pairT γ β) := snd_pair _ _
  have s2 : Γ ⊢[PRAAx] sndT (sndT (pairT q (pairT α (pairT γ β)))) ≐ pairT γ β := s1.sndE
  have hq : Γ ⊢[PRAAx] fstT (pairT q (pairT α (pairT γ β))) ≐ q := fst_pair _ _
  have hα : Γ ⊢[PRAAx] fstT (sndT (pairT q (pairT α (pairT γ β)))) ≐ α := s1.fstE
  have hγ : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT q (pairT α (pairT γ β))))) ≐ γ := s2.fstE
  have hβ : Γ ⊢[PRAAx] sndT (sndT (sndT (pairT q (pairT α (pairT γ β))))) ≐ β := s2.sndE
  exact congrMul (inJT_congr (.eqRefl _) hq hα hγ hβ) (congrEqb' (congrGcd (.eqRefl _) hq) (.eqRefl _))

/-- A product of bits is a bit: `sg(act) = [p/q ∈ J*][gcd = 1]`, here with `q = q'`. -/
theorem bit_eq {p q q' α γ β : PTm n} (hq : Γ ⊢[PRAAx] q ≐ q') :
    Γ ⊢[PRAAx] sg (actv p q α γ β) ≐ inJT p q' α γ β * eqb (gcd p q') one := by
  have h1 : Γ ⊢[PRAAx] le (sg (monus (p * β) (q * α))) one := sg_le_one _
  have h2 : Γ ⊢[PRAAx] le (sg (monus (q * γ) (p * β))) one := sg_le_one _
  have h3 : Γ ⊢[PRAAx] le (eqb (gcd p q) one) one := eqb_le_one _ _
  have hle : Γ ⊢[PRAAx] le (actv p q α γ β) one := by
    ipra_le sl h1 + 𝔞 (sg (monus (p * β) (q * α))) * sl h2 +
      𝔞 (sg (monus (p * β) (q * α))) * 𝔞 (sg (monus (q * γ) (p * β))) * sl h3
  exact (sg_of_le_one hle).eqTrans (congrMul (inJT_congr (.eqRefl _) hq (.eqRefl _) (.eqRefl _) (.eqRefl _))
    (congrEqb' (congrGcd (.eqRefl _) hq) (.eqRefl _)))

/-- The activity count of the scale `⌊Q/4⌋ < q ≤ Q` is `#𝓡 = redR Q`. -/
theorem scale_count {M Q T α γ β : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] ap2 (sumF (acB actK)) (monus Q (quo Q (num 4)) * M) (tup M (quo Q (num 4)) T α γ β) ≐
      redR Q (pairT M (pairT α (pairT γ β))) := by
  rw [acB_eq]
  refine (flatten gS (x := tl (quo Q (num 4)) T α γ β) hM (monus Q (quo Q (num 4)))).eqTrans ?_
  refine sum_congr_bounded _ _ (pairT M (tl (quo Q (num 4)) T α γ β))
    (pairT (succ (quo Q (num 4))) (pairT M (pairT α (pairT γ β)))) (monus Q (quo Q (num 4))) (.allI (.impI ?_))
  rw [LeanProofs.IPRA.inst2_offB, inst2_cqB,
    show Syn.shift (pairT M (tl (quo Q (num 4)) T α γ β)) = pairT (Syn.shift M)
      (tl (Syn.shift (quo Q (num 4))) (Syn.shift T) (Syn.shift α) (Syn.shift γ) (Syn.shift β)) by simp [Syn.shift],
    show Syn.shift (pairT (succ (quo Q (num 4))) (pairT M (pairT α (pairT γ β)))) =
      pairT (succ (Syn.shift (quo Q (num 4)))) (pairT (Syn.shift M) (pairT (Syn.shift α) (pairT (Syn.shift γ)
        (Syn.shift β)))) by simp [Syn.shift]]
  refine (LeanProofs.IPRA.oB_at gS _ _ _).eqTrans ?_
  refine .eqTrans ?_ (congrAp2 (sumF copB) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    (congrPairT (congrAdd (fst_pair _ _) (.eqRefl _)) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))).eqSymm
  refine sum_congr_bounded _ _ (pairT (var 0) (tl (Syn.shift (quo Q (num 4))) (Syn.shift T) (Syn.shift α)
      (Syn.shift γ) (Syn.shift β)))
    (pairT (succ (Syn.shift (quo Q (num 4))) + var 0) (pairT (Syn.shift α) (pairT (Syn.shift γ) (Syn.shift β))))
    (Syn.shift M) (.allI (.impI ?_))
  rw [LeanProofs.IPRA.inst2_rowB,
    show Syn.shift (pairT (var 0 : PTm (n + 1)) (tl (Syn.shift (quo Q (num 4))) (Syn.shift T) (Syn.shift α)
      (Syn.shift γ) (Syn.shift β))) = pairT (var 1) (tl (Syn.shift (Syn.shift (quo Q (num 4))))
        (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift α)) (Syn.shift (Syn.shift γ)) (Syn.shift (Syn.shift β))) by
      simp [Syn.shift],
    show Syn.shift (pairT (succ (Syn.shift (quo Q (num 4))) + var 0 : PTm (n + 1)) (pairT (Syn.shift α)
      (pairT (Syn.shift γ) (Syn.shift β)))) = pairT (succ (Syn.shift (Syn.shift (quo Q (num 4)))) + var 1)
        (pairT (Syn.shift (Syn.shift α)) (pairT (Syn.shift (Syn.shift γ)) (Syn.shift (Syn.shift β)))) by
      simp [Syn.shift]]
  exact (congrInst3 gS (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans
    ((row_pt _ _ _ _ _ _ _).eqTrans ((bit_eq (by ipra_ring)).eqTrans
      (cop_pt _ _ _ _ _).eqSymm))

/-- (K8) for `Q = 2^k ≤ M`: on the grid `T = Q! G` with `Q²w ≤ T`, the union `E` of the intervals of the
reduced fractions `p/q ∈ J*`, `⌊Q/4⌋ < q ≤ Q`, satisfies `DQ²w ≤ 16β|E|` and `β|E| ≤ 2DQ²w`. -/
theorem k8_bounds {α γ b0 M k R G w : PTm n} (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0))
    (hQM : Γ ⊢[PRAAx] le (pw two k) M) (hK : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * k))
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQR : Γ ⊢[PRAAx] le (pw two k) R)
    (hw : Γ ⊢[PRAAx] le (pw two k * pw two k * w) (fact R * G)) :
    Γ ⊢[PRAAx]
      le (monus γ α * (pw two k * pw two k) * w)
          (num 16 * succ b0 * measure (loB AK) (hiB AK actK) (fact R * G * M)
            (monus (pw two k) (quo (pw two k) (num 4)) * M)
            (pairT w (tup M (quo (pw two k) (num 4)) (fact R * G) α γ (succ b0)))) ⋏
        le (succ b0 * measure (loB AK) (hiB AK actK) (fact R * G * M)
            (monus (pw two k) (quo (pw two k) (num 4)) * M)
            (pairT w (tup M (quo (pw two k) (num 4)) (fact R * G) α γ (succ b0))))
          (num 2 * monus γ α * (pw two k * pw two k) * w) := by
  have hQ' : Γ ⊢[PRAAx] le (quo (pw two k) (num 4)) (pw two k) :=
    LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola.quo_le_self _ _
  have em := scale_measure (α := α) (γ := γ) (β := succ b0) hM hQ' hQR hw
  have ec := scale_count (T := fact R * G) (α := α) (γ := γ) (β := succ b0) (Q := pw two k) hM
  have k3 := k3_bounds hαγ hγ hQM hK
  have eE := natEq (em.eqTrans (congrMul (.eqRefl _) ec))
  have l1 := Prf.andE₁ k3
  have l2 := Prf.andE₂ k3
  exact .andI (by ipra_le 𝔞 w * sl l1 with (16 * 𝔞 b0 + 16) * eE)
    (by ipra_le 𝔞 w * sl l2 with (𝔞 b0 + 1) * eE)

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScaleCount
