import DiophantineConsistency.Sign17LinesTable

/-! SOURCE ONLY. Construct K's tile ranks and weighted word from the seed lines. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17LinesKernel

open scoped BigOperators
open CurrentKernel2011 Sign17LinesTable

def linePosition (i : Fin 942) : ℕ :=
  if i.val = 0 then 0 else 1 + ((lineOrderedRows.drop 1).map (fun row =>
    (2 ^ 44 - 1 + WangTiles942.selectorWeight row.2 -
      WangTiles942.selectorWeight (lineTile i)) / 2 ^ 44)).sum

theorem linePosition_eq (i : Fin 942) : linePosition i = WangTiles942.physicalPosition i := by
  simp only [linePosition, WangTiles942.physicalPosition, lineOrderedRows_eq, lineTile_eq]

def lineExponent : Term → ℕ
  | .inl j => exponent (.inl j)
  | .inr (.inl i) => 1005 - linePosition i
  | .inr (.inr e) => exponent (.inr (.inr e))

def lineCoefficient : Term → ℕ
  | .inl j => coefficient (.inl j)
  | .inr (.inl i) => 2 * WangTiles942.selectorWeight (lineTile i)
  | .inr (.inr e) => coefficient (.inr (.inr e))

theorem lineExponent_eq (t : Term) : lineExponent t = exponent t := by
  cases t with
  | inl j => rfl
  | inr e =>
    cases e with
    | inl i => simp only [lineExponent, exponent, position, linePosition_eq]
    | inr e => rfl

theorem lineCoefficient_eq (t : Term) : lineCoefficient t = coefficient t := by
  cases t with
  | inl j => rfl
  | inr e =>
    cases e with
    | inl i => simp only [lineCoefficient, coefficient, weight, lineTile_eq]
    | inr e => rfl

def lineK : ℕ := ∑ t : Term, lineCoefficient t * radix ^ lineExponent t

theorem lineK_eq : lineK = K := by
  unfold lineK K rawWord
  apply Finset.sum_congr rfl
  intro t _
  rw [lineCoefficient_eq, lineExponent_eq]

theorem lineK_bytes : lineK = Nat.ofDigits 256 Sign17KByteCompose.byteList := by
  rw [lineK_eq]
  exact Sign17KByteBinding.K_bytes.symm

end DiophantineConsistency.Sign17LinesKernel
#print axioms DiophantineConsistency.Sign17LinesKernel.linePosition_eq
#print axioms DiophantineConsistency.Sign17LinesKernel.lineK_eq
#print axioms DiophantineConsistency.Sign17LinesKernel.lineK_bytes
