import ZFCinPA.ValidatorEnvironmentSubstitution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA
open ValidatorEnvironmentLabels254 ValidatorEnvironmentSubstitution254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.term_labels_bShift
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.matches_qVec
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.term_labels_subst
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.vec_labels_subst
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.encode_subst
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.matches_pair
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.encode_subst_pair
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.encode_subst_two_bvars
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentSubstitution254.encode_subst_two_fvars

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example {n t : V} (ht : IsSemiterm ℒₛₑₜ n t) (F B z : V) :
    TermLabels.term F (z∷B) (termBShift ℒₛₑₜ t)=TermLabels.term F B t :=
  term_labels_bShift ht F B z
example {n m F B B' w : V} (hw : IsSemitermVec ℒₛₑₜ n m w)
    (he : Matches F B B' n w) (z : V) :
    Matches F (z∷B) (z∷B') (n+1) (qVec ℒₛₑₜ w) := matches_qVec hw he z
example {n F B B' w t : V} (ht : IsSemiterm ℒₛₑₜ n t) (he : Matches F B B' n w) :
    TermLabels.term F B (termSubst ℒₛₑₜ w t)=TermLabels.term F B' t := term_labels_subst ht he
example {n m k ts F B B' w : V} (ht : IsSemitermVec ℒₛₑₜ k n ts)
    (hw : IsSemitermVec ℒₛₑₜ n m w) (he : Matches F B B' n w) :
    TermLabels.vec F B k (termSubstVec ℒₛₑₜ k w ts)=TermLabels.vec F B' k ts :=
  vec_labels_subst ht hw he
example {n m p w : V} (hp : IsSemiformula ℒₛₑₜ n p) (hw : IsSemitermVec ℒₛₑₜ n m w)
    (F B B' s : V) (he : Matches F B B' n w) :
    encode F B s (subst ℒₛₑₜ w p)=encode F B' s p := encode_subst hp hw F B B' s he
example (F B t u : V) :
    Matches F B (TermLabels.term F B t∷TermLabels.term F B u∷0) 2 (t∷u∷0) :=
  matches_pair F B t u
example {m p t u : V} (hp : IsSemiformula ℒₛₑₜ 2 p)
    (ht : IsSemiterm ℒₛₑₜ m t) (hu : IsSemiterm ℒₛₑₜ m u) (F B s : V) :
    encode F B s (subst ℒₛₑₜ (t∷u∷0) p)=
      encode F (TermLabels.term F B t∷TermLabels.term F B u∷0) s p :=
  encode_subst_pair hp ht hu F B s
example {m p i j : V} (hp : IsSemiformula ℒₛₑₜ 2 p) (hi : i<m) (hj : j<m) (F B s : V) :
    encode F B s (subst ℒₛₑₜ (^#i∷^#j∷0) p)=encode F (B.[i]∷B.[j]∷0) s p :=
  encode_subst_two_bvars hp hi hj F B s
example {m p i j : V} (hp : IsSemiformula ℒₛₑₜ 2 p) (hi : i<m) (hj : j<m) (F B s : V) :
    encode F B s (subst ℒₛₑₜ (^#j∷^#i∷0) p)=encode F (B.[j]∷B.[i]∷0) s p :=
  encode_subst_two_bvars hp hj hi F B s
example {m p i : V} (hp : IsSemiformula ℒₛₑₜ 2 p) (hi : i<m) (F B s : V) :
    encode F B s (subst ℒₛₑₜ (^#i∷^#i∷0) p)=encode F (B.[i]∷B.[i]∷0) s p :=
  encode_subst_two_bvars hp hi hi F B s
example {p : V} (hp : IsSemiformula ℒₛₑₜ 2 p) (F B s i j : V) :
    encode F B s (subst ℒₛₑₜ (^&i∷^&j∷0) p)=
      encode F (freeLabel F i∷freeLabel F j∷0) s p := encode_subst_two_fvars hp F B s i j
