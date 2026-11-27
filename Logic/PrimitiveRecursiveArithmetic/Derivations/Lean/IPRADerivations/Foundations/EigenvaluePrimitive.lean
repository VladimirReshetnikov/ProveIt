import IPRADerivations.Foundations.PrimitiveScaling

/-!
# Integrality of an eigenvalue from a primitive eigenvector (`ipra_presentations_to_witnesses`, `lem:integer-eigenvalue`)

Packet: `foundations/ipra_presentations_to_witnesses`. "A vector `w ∈ ℤ^D` is primitive when
the greatest common divisor of `|w_1|, …, |w_D|` is one", and `lem:integer-eigenvalue`:
"`b` divides `a w_j`, and coprimality gives `b ∣ w_j`. ... Therefore `b ∣ 1`. Positivity of `b`
forces `b = 1`."

`Foundations/EigenvalueIntegral` proves `b = 1` from supplied Bezout coefficients of the
eigenvector. Here primitivity is the packet's definition: the list gcd `G_N` of
`Foundations/PrimitiveScaling` equals one. With `ω_j = |w_j|`, a seed `s` among the entries,
`La = |a|` and `gcd(b, La) = 1`:

* `eigen_integral_gcd`: if `b ∣ La ω_j` for `j < N`, `b ∣ La s`, and `G_N = 1`, then `b = 1`.

The step `b ∣ ω_j` is Gauss's lemma (`DiophantineNumberTheory/Coprime.gauss`), applied under
the bounded quantifier; then `b ∣ G_N` by `G_greatest`. No Bezout coefficients of the vector
are needed.
-/

namespace LeanProofs.IPRA.Foundations.EigenvaluePrimitive

open_ipra exports
open LeanProofs.IPRA.Foundations.PrimitiveScaling

variable {k : ℕ} {Γ : List (Fm PTm k)}

variable (ω : PTm 2)

/-- `lem:integer-eigenvalue`, integrality, with primitivity as "the gcd of the coordinates is
one": a reduced denominator `b` of an eigenvalue with a primitive eigenvector is `1`. -/
theorem eigen_integral_gcd {b La s x N : PTm k} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hg : Γ ⊢[PRAAx] gcd b La ≐ one)
    (hseed : Γ ⊢[PRAAx] dvd b (La * s))
    (hall : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      dvd (Syn.shift b) (Syn.shift La * inst2 ω (var 0) (Syn.shift x))))
    (hprim : Γ ⊢[PRAAx] G ω N s x ≐ one) : Γ ⊢[PRAAx] b ≐ one := by
  -- `b ∣ ω_j` for every `j < N`
  have hall' : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      dvd (Syn.shift b) (inst2 ω (var 0) (Syn.shift x))) := by
    refine .allI (.impI ?_)
    have hb' := hb.shift
    rw [shift_pos'] at hb'
    have hg' := hg.shift
    have eg : Fm.shift (gcd b La ≐ one) = (gcd (Syn.shift b) (Syn.shift La) ≐ one) := by
      ipra_ind_simp [Fm.shift, subst_ex2, Syn.shift]
    rw [eg] at hg'
    exact gauss hb'.wk hg'.wk (.impE hall.allOpen.wk Prf.hyp0)
  have d := G_greatest ω hb (gauss hb hg hseed) hall'
  exact eq_one_of_dvd_one hb (dvd_congr hprim d)

end LeanProofs.IPRA.Foundations.EigenvaluePrimitive
