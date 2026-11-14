import PA194SourceEquality
import PA194SeparationRelocation
namespace M6.PA.RelationalSource
open LO LO.FirstOrder
def sourceImply {ξ : Type} {n : Nat} (p q : Semiformula language ξ n) :=
  Semiformula.or (Semiformula.neg p) q

def sourceIff {ξ : Type} {n : Nat} (p q : Semiformula language ξ n) :=
  Semiformula.and (sourceImply p q) (sourceImply q p)

def liftMember (p : Semiproposition language 1) : Semiproposition language 3 :=
  Semiformula.rewAux (Rew.map (fun _ : Fin 1 => (0 : Fin 3)) id) p

def separationFormula (p : Semiproposition language 1) : Proposition language :=
  .all (.exs (.all (sourceIff (memAtom 1 0)
    (.and (memAtom 2 0) (liftMember p)))))


end M6.PA.RelationalSource

namespace PA194Logic.Relational.Source
open LO LO.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA194Logic PA194Logic.Relational

def sourceImplyNormalization {ξ : Type} {n : Nat} (p q : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo z : Nat) :
    Bi (relationalCode z (toNamed (sourceImply p q) b f lo))
      (wim (relationalCode z (toNamed p b f lo)) (relationalCode z (toNamed q b f lo))) :=
  ((negationProof p b f lo z).neg.trans
    (Bi.doubleNeg (relationalCode z (toNamed p b f lo))).symm).imp (Bi.refl _)

def sourceIffNormalization {ξ : Type} {n : Nat} (p q : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo z : Nat) :
    Bi (relationalCode z (toNamed (sourceIff p q) b f lo))
      (iffCode (relationalCode z (toNamed p b f lo)) (relationalCode z (toNamed q b f lo))) :=
  (sourceImplyNormalization p q b f lo z).and (sourceImplyNormalization q p b f lo z)

theorem toNamed_liftMember (p : Semiproposition language 1)
    (b : Fin 3 → Nat) (f : Nat → Nat) (lo : Nat) :
    toNamed (liftMember p) b f lo = toNamed p (fun _ => b 0) f lo := by
  apply toNamed_rew
  intro t
  cases t with
  | bvar i => rfl
  | fvar i => rfl
  | func fn _ => nomatch fn

def separationSupplier (p : Semiproposition language 1) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i,f i < lo) (hz : lo+3+depth p ≤ z) :
    Proof (code (separationFormula p) f lo z) := by
  let a := lo
  let c := lo+1
  let b := lo+1+1
  let body := toNamed p (fun _ => b) f (lo+1+1+1)
  have hbodyZ : body.names z = false :=
    toNamed_reserved p (fun _ => b) f (lo+1+1+1) z (by omega)
      (fun _ => by dsimp [b]; omega) (fun i => by have h := hf i; omega) (by omega)
  have hbodyC : body.names c = false :=
    toNamed_avoids p (fun _ => b) f (lo+1+1+1) c (by dsimp [c]; omega)
      (by dsimp [c]; omega) (fun _ => by dsimp [b,c]; omega)
      (fun i => by have h := hf i; dsimp [c]; omega)
  let raw := separationAtName a b c z body (by dsimp [a]; omega)
    (by dsimp [b]; omega) (by dsimp [c]; omega)
    (by dsimp [a,c]; omega) (by dsimp [b,c]; omega) hbodyZ hbodyC
  let env : Fin 3 → Nat := Fin.cases b (Fin.cases c (Fin.cases a Fin.elim0))
  let hn := sourceIffNormalization (memAtom 1 0) (.and (memAtom 2 0) (liftMember p))
    env f (lo+1+1+1) z
  have hn' : Bi (relationalCode z (toNamed
      (sourceIff (memAtom 1 0) (.and (memAtom 2 0) (liftMember p))) env f (lo+1+1+1)))
      (iffCode (wel c b) (wa (wel a b) (relationalCode z body))) := by
    have hprop := toNamed_liftMember p env f (lo+1+1+1)
    simp only [toNamed,relationalCode,memAtom,atomNamed,termLabel,Matrix.cons_val_zero,
      Matrix.cons_val_one,hprop] at hn
    exact hn
  exact .mp (.all a raw) (((hn'.all b).exs c).all a).2

#print axioms separationSupplier
end PA194Logic.Relational.Source

