import IPRADerivations.DiophantineNumberTheory.KhinchinDyadic
import IPRADerivations.DiophantineNumberTheory.KhinchinAmplify

/-!
# One unit of tail mass supplies the block (`hurwitz_khinchin_ipra`, `S ≥ 1`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"One call to the divergence modulus
supplies the block": "Monotonicity gives `1 ≤ Σ_{q=s}^{D(s)} ψ(q) ≤ Σ_{k=K}^B 2^k ψ(2^k)`. For any finite
nonnegative rational list `(a_k)`, `Σ_k min(a_k, 1) ≥ min(Σ_k a_k, 1)`. … Hence `S ≥ 1`, as required for (K11)."

With `ψ = Ψ/C` (a natural-valued numerator over the denominator `C`), `s = 2^K` and `D(s) < 2^{K+B}`, the divergence
modulus (K-D) reads, cleared, `C + Σ_{q<2^K} Ψ(q) ≤ Σ_{q<2^{K+B}} Ψ(q)`. Then:

* `tail_mass`: `C ≤ Σ_{k<B} 2^{K+k} Ψ(2^{K+k})` — by the dyadic majorant `KhinchinDyadic.dyadic`;
* `S_ge_one`: `C ≤ Σ_{k<B} min(2^{K+k} Ψ(2^{K+k}), C)`, i.e. `S = Σ_k t_k ≥ 1` for the capped scale masses
  `t_k = min(2^{K+k} ψ(2^{K+k}), 1)` — by `KhinchinAmplify.min_sum` and `mn_right`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinTailMass

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinDyadic (dyB dyadic)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinAmplify (mn MB min_sum mn_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The divergence modulus and the dyadic majorant: `C ≤ Σ_{k<B} 2^{K+k} Ψ(2^{K+k})`. -/
theorem tail_mass (Ψ : PTm 2) (K B x : PTm n) {C : PTm n}
    (hD : Γ ⊢[PRAAx] le (C + ap2 (sumF Ψ) (pw two K) x) (ap2 (sumF Ψ) (pw two (K + B)) x))
    (hblk : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (ap2 (sumF (offB Ψ)) (pw two (Syn.shift K + var 0)) (pairT (pw two (Syn.shift K + var 0)) (Syn.shift x)))
        (pw two (Syn.shift K + var 0) * inst2 Ψ (pw two (Syn.shift K + var 0)) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le C (ap2 (sumF (dyB Ψ)) B (pairT K x)) := by
  have d := dyadic Ψ K B x hblk
  ipra_le sl hD + sl d

/-- `S ≥ 1`: `C ≤ Σ_{k<B} min(2^{K+k} Ψ(2^{K+k}), C)`. -/
theorem S_ge_one (Ψ : PTm 2) (K B x : PTm n) {C : PTm n}
    (hD : Γ ⊢[PRAAx] le (C + ap2 (sumF Ψ) (pw two K) x) (ap2 (sumF Ψ) (pw two (K + B)) x))
    (hblk : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (ap2 (sumF (offB Ψ)) (pw two (Syn.shift K + var 0)) (pairT (pw two (Syn.shift K + var 0)) (Syn.shift x)))
        (pw two (Syn.shift K + var 0) * inst2 Ψ (pw two (Syn.shift K + var 0)) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le C (ap2 (sumF (MB (dyB Ψ))) B (pairT C (pairT K x))) :=
  le_congr (mn_right (tail_mass Ψ K B x hD hblk)) (.eqRefl _) (min_sum (dyB Ψ) B C (pairT K x))

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinTailMass
