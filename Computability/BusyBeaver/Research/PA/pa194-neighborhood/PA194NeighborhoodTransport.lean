import PA194Neighborhood
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194Logic

def iffVacuity (x a b : Nat)
    (ha : Derivation (wim a (wal x a))) (hb : Derivation (wim b (wal x b))) :
    Derivation (wim (iffCode a b) (wal x (iffCode a b))) :=
  conjunctionVacuity x _ _ (implicationVacuity x a b ha hb) (implicationVacuity x b a hb ha)

def iffTransport (e a0 a1 b0 b1 : Nat)
    (ha : Derivation (wim e (iffCode a1 a0)))
    (hb : Derivation (wim e (iffCode b1 b0))) :
    Derivation (wim e (wim (iffCode a0 b0) (iffCode a1 b1))) := by
  let he : Context [iffCode a0 b0,e] e := .assumption (by simp)
  let hp : Context [iffCode a0 b0,e] (iffCode a0 b0) := .assumption (by simp)
  let hA : Context [iffCode a0 b0,e] (iffCode a1 a0) := .mp he (.closed ha)
  let hB : Context [iffCode a0 b0,e] (iffCode b1 b0) := .mp he (.closed hb)
  let forward := (hA.andLeft.arrowCompose hp.andLeft).arrowCompose hB.andRight
  let backward := (hB.andLeft.arrowCompose hp.andRight).arrowCompose hA.andRight
  exact (Context.andIntro forward backward).deduction.deduction.empty

def leftMatrix (a b z : Nat) := iffCode (wel a z) (wel b z)
def rightMatrix (a b z : Nat) := iffCode (wel z a) (wel z b)

def leftMatrixVacuity (a b z x : Nat) (hxa : x ≠ a) (hxb : x ≠ b) (hxz : x ≠ z) :
    Derivation (wim (leftMatrix a b z) (wal x (leftMatrix a b z))) :=
  iffVacuity x _ _ (membershipVacuity a z x hxa hxz) (membershipVacuity b z x hxb hxz)

def rightMatrixVacuity (a b z x : Nat) (hxa : x ≠ a) (hxb : x ≠ b) (hxz : x ≠ z) :
    Derivation (wim (rightMatrix a b z) (wal x (rightMatrix a b z))) :=
  iffVacuity x _ _ (membershipVacuity z a x hxz hxa) (membershipVacuity z b x hxz hxb)

def leftMatrixRewrite (a b z z0 : Nat) :
    Derivation (wim (weq z z0) (wim (leftMatrix a b z0) (leftMatrix a b z))) :=
  iffTransport _ _ _ _ _ (membershipRightIff z z0 a) (membershipRightIff z z0 b)

def rightMatrixRewrite (a b z z0 : Nat) :
    Derivation (wim (weq z z0) (wim (rightMatrix a b z0) (rightMatrix a b z))) :=
  iffTransport _ _ _ _ _ (membershipLeftIff z z0 a) (membershipLeftIff z z0 b)

/-- Transfer a universally quantified formula along an explicitly proved rewrite. -/
def transferBinder (z0 z atom target : Nat)
    (hvTarget : Derivation (wim target (wal z0 target)))
    (hvAntecedent : Derivation (wim (wal z0 atom) (wal z (wal z0 atom))))
    (hr : Derivation (wim (weq z z0) (wim atom target))) :
    Derivation (wim (wal z0 atom) (wal z target)) := by
  have hs := specializeWithMirroredEquality z0 z atom target hvTarget hr
  have hu : Derivation (wim (wal z (wal z0 atom)) (wal z target)) :=
    .mp (.all z hs) (r2 z (wal z0 atom) target)
  exact implicationCompose hvAntecedent hu

/-- All permitted neighborhood binders, including the self-code collision. -/
def primitiveToNeighborhood (a b z : Nat) (hza : z ≠ a) (hzb : z ≠ b) :
    Derivation (wim (weq a b) (neighborhood a b z)) := by
  let z0 := weq a b
  by_cases hz : z = z0
  · subst z
    exact primitiveToSelfNeighborhood a b
  · have h0a : z0 ≠ a := by
      have h := (equalityCode_fresh a b).1
      omega
    have h0b : z0 ≠ b := by
      have h := (equalityCode_fresh a b).2
      omega
    have h0z : z0 ≠ z := Ne.symm hz
    have hLtarget := leftMatrixVacuity a b z z0 h0a h0b h0z
    have hRtarget := rightMatrixVacuity a b z z0 h0a h0b h0z
    have hLsource := leftMatrixVacuity a b z0 z hza hzb hz
    have hRsource := rightMatrixVacuity a b z0 z hza hzb hz
    have hL := transferBinder z0 z (leftMatrix a b z0) (leftMatrix a b z)
      hLtarget (universalVacuity z z0 _ hLsource) (leftMatrixRewrite a b z z0)
    have hR := transferBinder z0 z (rightMatrix a b z0) (rightMatrix a b z)
      hRtarget (universalVacuity z z0 _ hRsource) (rightMatrixRewrite a b z z0)
    let he : Context [weq a b] (weq a b) := .assumption (by simp)
    let hs : Context [weq a b] (neighborhood a b z0) :=
      .mp he (.closed (primitiveToSelfNeighborhood a b))
    have hl : Context [weq a b] (wal z (leftMatrix a b z)) :=
      .mp hs.andLeft (.closed hL)
    have hr : Context [weq a b] (wal z (rightMatrix a b z)) :=
      .mp hs.andRight (.closed hR)
    exact (Context.andIntro hl hr).deduction.empty

def iffSymmetry (a b : Nat) : Derivation (wim (iffCode a b) (iffCode b a)) := by
  let h : Context [iffCode a b] (wa (wim a b) (wim b a)) := .assumption (by simp [iffCode])
  exact (Context.andIntro h.andRight h.andLeft).deduction.empty

def neighborhoodSymmetry (a b z : Nat) :
    Derivation (wim (neighborhood a b z) (neighborhood b a z)) := by
  let h : Context [neighborhood a b z] (neighborhood a b z) := .assumption (by simp)
  let l := h.andLeft.forallMP z (.closed (.all z (iffSymmetry (wel a z) (wel b z))))
  let r := h.andRight.forallMP z (.closed (.all z (iffSymmetry (wel z a) (wel z b))))
  exact (Context.andIntro l r).deduction.empty

def neighborhoodWitness (x c z : Nat) (hzx : z ≠ x) (hzc : z ≠ c) :
    Derivation (wex x (neighborhood x c z)) :=
  .mp (.mp (r1 x c) (existentialMonotonicity x (primitiveToNeighborhood c x z hzc hzx)))
    (existentialMonotonicity x (neighborhoodSymmetry c x z))

#print axioms primitiveToNeighborhood
#print axioms neighborhoodWitness
#print axioms iffTransport
#print axioms leftMatrixVacuity
#print axioms rightMatrixVacuity
#print axioms leftMatrixRewrite
#print axioms rightMatrixRewrite
#print axioms transferBinder
end PA194Logic
