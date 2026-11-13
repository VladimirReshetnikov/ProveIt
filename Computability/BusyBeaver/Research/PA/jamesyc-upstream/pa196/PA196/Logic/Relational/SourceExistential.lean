module
public import PA196.Logic.Relational.SourceInstantiation
public import PA196.Logic.Relational.SourceNegation
@[expose] public section

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA196.Logic PA196.Logic.Relational

theorem depth_neg {ξ : Type} {n : Nat} (p : Semiformula language ξ n) :
    depth (Semiformula.neg p) = depth p := by
  induction p <;> simp_all [Semiformula.neg, depth]

theorem instantiate_neg {ξ : Type} {n : Nat} (p : Semiformula language ξ (n+1))
    (t : Semiterm language ξ n) :
    instantiate (Semiformula.neg p) t = Semiformula.neg (instantiate p t) :=
  Semiformula.rewAux_neg _ _

def existentialInstance {ξ : Type} {n : Nat} (p : Semiformula language ξ (n+1))
    (t : Semiterm language ξ n) (b : Fin n → Nat) (f : ξ → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hb : ∀ i,b i < lo) (hf : ∀ i,f i < lo)
    (hz : lo+1+depth p ≤ z) :
    Proof (wim (relationalCode z (toNamed (instantiate p t) b f lo))
      (relationalCode z (toNamed (.exs p) b f lo))) := by
  let u := universalInstance (Semiformula.neg p) t b f lo z hlo hb hf
    (by simpa only [depth_neg] using hz)
  rw [instantiate_neg] at u
  let hn := negationProof (instantiate p t) b f lo z
  let start := implicationCompose (doubleNegationIntroduction
    (relationalCode z (toNamed (instantiate p t) b f lo))) (contrapose hn.1)
  let finish := ((negationProof p (Fin.cases lo b) f (lo+1) z).all lo).neg
  exact implicationCompose (implicationCompose start (contrapose u)) finish.1

#print axioms existentialInstance
end PA196.Logic.Relational.Source

