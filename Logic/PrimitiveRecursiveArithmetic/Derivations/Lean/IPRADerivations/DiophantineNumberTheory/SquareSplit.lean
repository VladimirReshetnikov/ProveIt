import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.CertificateTactics

/-!
# Coprime cancellation and square splitting

Packet: `mordell_weil_ipra`, `paper/01_foundations.tex`, Lemma `lem:squares`:

1. `gcd(a, b) = 1` and `a ∣ bc` give `a ∣ c` (`Coprime.gauss`);
2. `d > 0` and `d² ∣ c²` give `d ∣ c` (`Coprime.dvd_of_sq_dvd_sq`);
3. `a, b, c > 0`, `gcd(a, b) = 1` and `ab = c²` give `a = r²`, `b = s²` and `c = rs` with the explicit
   witnesses `r = gcd(a, c)`, `s = gcd(b, c)` (`square_split`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.SquareSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `lem:squares` (3): `a = r²`, `b = s²`, `c = r s` for `r = gcd(a, c)`, `s = gcd(b, c)`. -/
theorem square_split {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hg : Γ ⊢[PRAAx] gcd a b ≐ one) (h : Γ ⊢[PRAAx] a * b ≐ c * c) :
    Γ ⊢[PRAAx] (a ≐ gcd a c * gcd a c) ⋏ ((b ≐ gcd b c * gcd b c) ⋏ (c ≐ gcd a c * gcd b c)) := by
  have ra := square_of_coprime ha hg h
  have sb := square_of_coprime hb (gcd_comm_one hb hg) ((mul_comm _ _).eqTrans h)
  refine .andI ra (.andI sb ?_)
  refine sq_inj ?_
  ipra_lc -natEq h + 𝔞 b * natEq ra + 𝔞 (gcd a c) * 𝔞 (gcd a c) * natEq sb

end LeanProofs.IPRA.DiophantineNumberTheory.SquareSplit
