import DiophantineConsistency.Compact44.FreeJExactOrdinary
import DiophantineConsistency.Compact44.FreeJPowerFinish

/-! # The six ordinary facts the compact44 halting chain consumes

The halting chain from `FixedGraphMarkedHaltDraft.graph_halts` down to the
free-J literal has 60 theorems with a literal-zero hypothesis `hz`. Of these,
54 only pass `hz` on. Six unpack it: the exact Pell indices, the first-factor
transport, the first-pair congruence, `X = 2^R`, `q ∣ 3X`, and `q³ ∣ Y`.

`LeafFacts p v` bundles exactly those six conclusions, each under the
port-bound hypotheses of its original lemma. Two theorems use it:

* `CompactLeafFactsLiteral.of_literal` derives it from a positive free-J zero;
* the `_facts` copies of the forwarders in `Compact44/Facts/` take it in
  place of `hz`.

Any other equation on the compact44 tuple therefore reaches halting by
proving `LeafFacts` at a valuation whose coordinates `0 1 2 5 6 8 9` read
`J F α X Y η ζ`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactLeafFacts
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellCongruences
open DiophantineConsistency.ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure LeafFacts (p : Fin 4 → ℕ) (v : Fin 12 → V) : Prop where
  indices : 0<(p 0:V) → (p 2:V)<(p 0:V) → (p 3:V)<2*(p 0:V) →
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let a : V := v 5*v 6+v 6
    let c : V := v 8+v 6*(v 8+v 9)
    ∃ first main j pi : V, 0<first ∧ 0<main ∧ 13≤j ∧ j<pi ∧ pi=R ∧ 2*j=R+1 ∧
      xcoord j (2*((v 5*v 6)*v 6-1)+1)=first ∧
      2*ycoord j (2*((v 5*v 6)*v 6-1)+1)=v 8+v 9 ∧
      xcoord pi a=main ∧ ycoord pi a=c
  transport : 0<(p 0:V) →
    let q : V := 1+v 0*(p 0:V)
    0<q-(v 1+v 2)
  pairMod : 0<(p 0:V) →
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let A : V := v 5+(p 1:V)*q
    ((v 1+v 2)*A+v 1*q)%b=(q*A)%b
  power : 0<(p 0:V) → (p 2:V)<(p 0:V) → (p 3:V)<2*(p 0:V) → (46:V)≤(p 0:V) →
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    v 5=Exp.exp R
  projection : 0<(p 0:V) → (p 2:V)<(p 0:V) → (p 3:V)<2*(p 0:V) →
    let q : V := 1+v 0*(p 0:V)
    q ∣ 3*v 5 ∧ q≤3*v 5
  ydiv : 0 < v 0 → 0 < (p 0:V) → (1+v 0*(p 0:V))^3 ∣ v 6

end CompactLeafFacts
