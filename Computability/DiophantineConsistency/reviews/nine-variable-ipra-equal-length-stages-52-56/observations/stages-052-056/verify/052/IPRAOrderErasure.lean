import DiophantineConsistency.IPRAEqualityOnlyReference

/-!
Syntactic elimination of the native less-than relation. The relation is read
as the PR comparison code equal to one. This file does not yet prove that
erasure commutes with substitutions, transports derivations or identifies the
reference and native theories.
-/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAOrderErasure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRATheory PRALanguage IPRAQuantifierFree
open IPRAEqualityOnlyReference

/-- Term translation uses only `func`; the relation component is irrelevant. -/
def termsToReference : PRALanguage.language →ᵥ IPRAEqualityOnlyReference.language where
  func := fun f => f
  rel := fun r => match r with
    | .eq => EqualityRel.eq
    | .lt => EqualityRel.eq

def toNative : IPRAEqualityOnlyReference.language →ᵥ PRALanguage.language where
  func := fun f => f
  rel := fun r => match r with
    | .eq => Language.ORing.Rel.eq

def embed {ξ : Type} : ∀ {n : ℕ},
    Semiformulaᵢ IPRAEqualityOnlyReference.language ξ n → Semiformulaᵢ PRALanguage.language ξ n
  | _, .falsum => .falsum
  | _, .rel .eq v => .rel Language.ORing.Rel.eq (fun i => Semiterm.lMap toNative (v i))
  | _, .and φ ψ => .and (embed φ) (embed ψ)
  | _, .or φ ψ => .or (embed φ) (embed ψ)
  | _, .imp φ ψ => .imp (embed φ) (embed ψ)
  | _, .all φ => .all (embed φ)
  | _, .exs φ => .exs (embed φ)

def erase {ξ : Type} : ∀ {n : ℕ},
    Semiformulaᵢ PRALanguage.language ξ n → Semiformulaᵢ IPRAEqualityOnlyReference.language ξ n
  | _, .falsum => .falsum
  | _, .rel .eq v => .rel EqualityRel.eq (fun i => Semiterm.lMap termsToReference (v i))
  | _, .rel .lt v => .rel EqualityRel.eq
      ![.func ltBitCode (fun i => Semiterm.lMap termsToReference (v i)),
        .func oneCode Fin.elim0]
  | _, .and φ ψ => .and (erase φ) (erase ψ)
  | _, .or φ ψ => .or (erase φ) (erase ψ)
  | _, .imp φ ψ => .imp (erase φ) (erase ψ)
  | _, .all φ => .all (erase φ)
  | _, .exs φ => .exs (erase φ)

theorem term_roundtrip {ξ : Type} {n : ℕ}
    (t : Semiterm IPRAEqualityOnlyReference.language ξ n) :
    Semiterm.lMap termsToReference (Semiterm.lMap toNative t) = t := by
  induction t with
  | bvar i => rfl
  | fvar i => rfl
  | func f v ih =>
    simp only [Semiterm.lMap_func, termsToReference, toNative]
    congr 1
    funext i
    exact ih i

theorem erase_embed {ξ : Type} {n : ℕ}
    (φ : Semiformulaᵢ IPRAEqualityOnlyReference.language ξ n) : erase (embed φ) = φ := by
  induction φ with
  | falsum => rfl
  | rel r v =>
    cases r
    simp only [embed, erase]
    congr 1
    funext i
    exact term_roundtrip (v i)
  | and φ ψ ihφ ihψ => simp [embed, erase, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [embed, erase, ihφ, ihψ]
  | imp φ ψ ihφ ihψ => simp [embed, erase, ihφ, ihψ]
  | all φ ih => simp [embed, erase, ih]
  | exs φ ih => simp [embed, erase, ih]

theorem erase_preserves_open {ξ : Type} {n : ℕ}
    (φ : Semiformulaᵢ PRALanguage.language ξ n) : OpenI φ → OpenI (erase φ) := by
  induction φ with
  | falsum => simp [erase, OpenI]
  | rel r v => cases r <;> simp [erase, OpenI]
  | and φ ψ ihφ ihψ => simp only [erase, OpenI]; exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | or φ ψ ihφ ihψ => simp only [erase, OpenI]; exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | imp φ ψ ihφ ihψ => simp only [erase, OpenI]; exact fun h => ⟨ihφ h.1, ihψ h.2⟩
  | all φ ih => simp [OpenI]
  | exs φ ih => simp [OpenI]

end DiophantineConsistency.IPRAOrderErasure
