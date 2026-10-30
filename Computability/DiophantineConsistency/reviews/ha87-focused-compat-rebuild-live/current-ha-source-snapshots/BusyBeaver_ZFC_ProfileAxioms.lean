import BusyBeaver.ZFC.ProfileComposition

/-!
Set-existence lemmas for the equality-free bisimulation interpretation.

Every collection resource below is an explicitly named relation instance.
Theorems with predicates P or R require their invariance under the represented
equivalence; they do not assume collection for arbitrary semantic relations.
The final Infinity lemma supplies a singleton-closed container (INF_lib),
not yet the ordinary von Neumann inductive-set axiom.
-/

namespace SetTheory.BusyBeaver.ZFC.ProfileAxioms

open Profile ProfilePairs ProfileCollection ProfileComposition

universe u
variable {V : Type u}

theorem same_eqv (mem : V → V → Prop) (hRefl : ∀ x, Eqv mem x x)
    {x y : V} (hxy : Same mem x y) : Eqv mem x y := by
  obtain ⟨r, hBis, hxx⟩ := hRefl x
  exact ⟨r, hBis, app_congr mem (same_refl mem x) hxy hxx⟩

theorem raw_member (mem : V → V → Prop) (hRefl : ∀ x, Eqv mem x x)
    {x y : V} (hxy : mem x y) : Member mem x y := ⟨x, hxy, hRefl x⟩

theorem member_left (mem : V → V → Prop)
    (hSymm : ∀ x y, Eqv mem x y → Eqv mem y x)
    (hTrans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z)
    {x x' y : V} (hxx' : Eqv mem x x') (hxy : Member mem x y) : Member mem x' y := by
  obtain ⟨a, hay, hxa⟩ := hxy
  exact ⟨a, hay, hTrans x' x a (hSymm x x' hxx') hxa⟩

theorem member_right (mem : V → V → Prop)
    (hTrans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z)
    {x y y' : V} (hyy' : Eqv mem y y') (hxy : Member mem x y) : Member mem x y' := by
  obtain ⟨r, hBis, hRoot⟩ := hyy'
  obtain ⟨a, hay, hxa⟩ := hxy
  obtain ⟨b, hby', hab⟩ := (hBis y y' hRoot).1 a hay
  exact ⟨b, hby', hTrans x a b hxa ⟨r, hBis, hab⟩⟩

theorem member_left_iff (mem : V → V → Prop)
    (hSymm : ∀ x y, Eqv mem x y → Eqv mem y x)
    (hTrans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z)
    {x x' y : V} (hxx' : Eqv mem x x') : Member mem x y ↔ Member mem x' y :=
  ⟨member_left mem hSymm hTrans hxx',
    member_left mem hSymm hTrans (hSymm x x' hxx')⟩

theorem empty_of_raw_empty (mem : V → V → Prop) (e : V)
    (he : ∀ z, ¬ mem z e) : ∀ z, ¬ Member mem z e :=
  fun _ ⟨a, hae, _⟩ => he a hae

theorem pair_of_profile (mem : V → V → Prop)
    (hRefl : ∀ x, Eqv mem x x)
    (hTrans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z)
    (a b p : V) (hp : Pair mem p a b) :
    ∀ z, Member mem z p ↔ Eqv mem z a ∨ Eqv mem z b := by
  intro z
  constructor
  · rintro ⟨v, hvp, hzv⟩
    rcases (hp v).mp ⟨v, hvp, same_refl mem v⟩ with hva | hvb
    · exact Or.inl (hTrans z v a hzv (same_eqv mem hRefl hva))
    · exact Or.inr (hTrans z v b hzv (same_eqv mem hRefl hvb))
  · rintro (hza | hzb)
    · obtain ⟨v, hvp, hav⟩ := (hp a).mpr (Or.inl (same_refl mem a))
      exact ⟨v, hvp, hTrans z a v hza (same_eqv mem hRefl hav)⟩
    · obtain ⟨v, hvp, hbv⟩ := (hp b).mpr (Or.inr (same_refl mem b))
      exact ⟨v, hvp, hTrans z b v hzb (same_eqv mem hRefl hbv)⟩

/-- The existing approximate-union template preserves every raw profile. -/
theorem union_profile_of_instance (mem : V → V → Prop) (a : V)
    (hContainers : Containers mem)
    (hCollect : CollectionInstance mem (UnionChoice mem a)) :
    ∃ b, ∀ z, ClassMember mem z b ↔ ∃ x, mem x a ∧ ClassMember mem z x := by
  obtain ⟨domain, haDomain, hTrans, _⟩ := hContainers a
  obtain ⟨b, hSupport, hCover⟩ := hCollect domain
  refine ⟨b, fun z => ?_⟩
  constructor
  · rintro ⟨v, hvb, hzv⟩
    obtain ⟨d, ⟨x, hxa, hdx⟩, hvd⟩ := hSupport v hvb
    exact ⟨x, hxa, d, hdx, same_trans mem hzv hvd⟩
  · rintro ⟨x, hxa, d, hdx, hzd⟩
    obtain ⟨v, hvb, _, hvd⟩ := hCover d (hTrans x (hTrans a haDomain x hxa) d hdx)
      ⟨d, ⟨x, hxa, hdx⟩, same_refl mem d⟩
    exact ⟨v, hvb, same_trans mem hzd (same_symm mem hvd)⟩

theorem union_of_instance (mem : V → V → Prop) (a : V)
    (hContainers : Containers mem)
    (hRefl : ∀ x, Eqv mem x x)
    (hTrans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z)
    (hCollect : CollectionInstance mem (UnionChoice mem a)) :
    ∃ b, ∀ z, Member mem z b ↔ ∃ x, Member mem x a ∧ Member mem z x := by
  obtain ⟨b, hb⟩ := union_profile_of_instance mem a hContainers hCollect
  refine ⟨b, fun z => ?_⟩
  constructor
  · rintro ⟨v, hvb, hzv⟩
    obtain ⟨x, hxa, d, hdx, hvd⟩ := (hb v).mp ⟨v, hvb, same_refl mem v⟩
    exact ⟨x, raw_member mem hRefl hxa, d, hdx,
      hTrans z v d hzv (same_eqv mem hRefl hvd)⟩
  · rintro ⟨x, ⟨v, hva, hxv⟩, hzx⟩
    obtain ⟨d, hdv, hzd⟩ := member_right mem hTrans hxv hzx
    obtain ⟨w, hwb, hdw⟩ := (hb d).mpr ⟨v, hva, d, hdv, same_refl mem d⟩
    exact ⟨w, hwb, hTrans z d w hzd (same_eqv mem hRefl hdw)⟩

def SubD (mem : V → V → Prop) (r a : V) : Prop :=
  ∀ z, mem z r → ClassMember mem z a

def InterpretedSub (mem : V → V → Prop) (x a : V) : Prop :=
  ∀ z, Member mem z x → Member mem z a

def SeparationChoice (mem : V → V → Prop) (a : V) (p : V → Prop) (x y : V) : Prop :=
  mem x a ∧ Same mem y x ∧ p x

/-- The trace is only a SubD trace, which suffices for interpreted Separation. -/
theorem separation_of_instance (mem : V → V → Prop) (a : V) (p : V → Prop)
    (hRefl : ∀ x, Eqv mem x x)
    (hTrans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z)
    (hInvariant : ∀ x y, Eqv mem x y → (p x ↔ p y))
    (hCollect : CollectionInstance mem (SeparationChoice mem a p)) :
    ∃ b, SubD mem b a ∧ ∀ z, Member mem z b ↔ Member mem z a ∧ p z := by
  obtain ⟨b, hSupport, hCover⟩ := hCollect a
  refine ⟨b, fun v hvb => ?_, fun z => ⟨?_, ?_⟩⟩
  · obtain ⟨x, hxa, hvx, _⟩ := hSupport v hvb
    exact ⟨x, hxa, hvx⟩
  · rintro ⟨v, hvb, hzv⟩
    obtain ⟨x, hxa, hvx, hpx⟩ := hSupport v hvb
    have hzx := hTrans z v x hzv (same_eqv mem hRefl hvx)
    exact ⟨⟨x, hxa, hzx⟩, (hInvariant z x hzx).mpr hpx⟩
  · rintro ⟨⟨x, hxa, hzx⟩, hpz⟩
    obtain ⟨v, hvb, _, hvx, _⟩ := hCover x hxa
      ⟨x, hxa, same_refl mem x, (hInvariant z x hzx).mp hpz⟩
    exact ⟨v, hvb, hTrans z x v hzx (same_eqv mem hRefl (same_symm mem hvx))⟩

/-- All profile traces of a have a common raw-membership bound. -/
theorem subD_bound (mem : V → V → Prop) (a : V) (hContainers : Containers mem) :
    ∃ q, ∀ r, SubD mem r a → mem r q := by
  obtain ⟨v, hav, hTransV, _⟩ := hContainers a
  obtain ⟨w, hvw, _, hPowerW⟩ := hContainers v
  obtain ⟨b, hbw, hb⟩ := hPowerW v hvw
  obtain ⟨q, _, hq⟩ := hPowerW b hbw
  refine ⟨q, fun r hr => hq r fun z hzr => ?_⟩
  obtain ⟨x, hxa, hzx⟩ := hr z hzr
  exact hb z fun t htz => hTransV x (hTransV a hav x hxa) t ((hzx t).mp htz)

def PowerChoice (mem : V → V → Prop) (a bound x y : V) : Prop :=
  mem x bound ∧ Same mem y x ∧ SubD mem x a

theorem power_profile_of_instance (mem : V → V → Prop) (a bound : V)
    (hBound : ∀ r, SubD mem r a → mem r bound)
    (hCollect : CollectionInstance mem (PowerChoice mem a bound)) :
    ∃ p, (∀ v, mem v p → SubD mem v a) ∧
      ∀ r, SubD mem r a → ClassMember mem r p := by
  obtain ⟨p, hSupport, hCover⟩ := hCollect bound
  refine ⟨p, fun v hvp z hzv => ?_, fun r hr => ?_⟩
  · obtain ⟨r, _, hvr, hr⟩ := hSupport v hvp
    exact hr z ((hvr z).mp hzv)
  · obtain ⟨v, hvp, _, hvr, _⟩ := hCover r (hBound r hr)
      ⟨r, hBound r hr, same_refl mem r, hr⟩
    exact ⟨v, hvp, same_symm mem hvr⟩

/-- Interpreted Power Set, using only the indicated trace and bounded-filter instances. -/
theorem power_of_instances (mem : V → V → Prop) (a : V)
    (hContainers : Containers mem)
    (hRefl : ∀ x, Eqv mem x x)
    (hSymm : ∀ x y, Eqv mem x y → Eqv mem y x)
    (hTrans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z)
    (hExt : ∀ x y, (∀ z, Member mem z x ↔ Member mem z y) → Eqv mem x y)
    (hTraces : ∀ x, CollectionInstance mem
      (SeparationChoice mem a (fun z => Member mem z x)))
    (hPowers : ∀ bound, CollectionInstance mem (PowerChoice mem a bound)) :
    ∃ p, ∀ x, Member mem x p ↔ InterpretedSub mem x a := by
  obtain ⟨bound, hBound⟩ := subD_bound mem a hContainers
  obtain ⟨p, hSupport, hCover⟩ := power_profile_of_instance mem a bound hBound (hPowers bound)
  refine ⟨p, fun x => ?_⟩
  constructor
  · rintro ⟨v, hvp, hxv⟩ z hzx
    obtain ⟨t, htv, hzt⟩ := member_right mem hTrans hxv hzx
    obtain ⟨u, hua, htu⟩ := hSupport v hvp t htv
    exact ⟨u, hua, hTrans z t u hzt (same_eqv mem hRefl htu)⟩
  · intro hx
    obtain ⟨r, hrTrace, hr⟩ := separation_of_instance mem a (fun z => Member mem z x)
      hRefl hTrans (fun u v huv => member_left_iff mem hSymm hTrans huv) (hTraces x)
    have hxr : Eqv mem x r :=
      hExt x r fun z => ⟨fun hz => (hr z).mpr ⟨hx z hz, hz⟩, fun hz => ((hr z).mp hz).2⟩
    obtain ⟨v, hvp, hrv⟩ := hCover r hrTrace
    exact ⟨v, hvp, hTrans x r v hxr (same_eqv mem hRefl hrv)⟩

def ReplacementChoice (mem : V → V → Prop) (a : V)
    (r : V → V → Prop) (x y : V) : Prop := mem x a ∧ r x y

/-- Partial functional image; functionality is with respect to Eqv, not raw equality. -/
theorem replacement_of_instance (mem : V → V → Prop) (a : V) (r : V → V → Prop)
    (hRefl : ∀ x, Eqv mem x x)
    (hSymm : ∀ x y, Eqv mem x y → Eqv mem y x)
    (hInvariant : ∀ x x' y y', Eqv mem x x' → Eqv mem y y' → (r x y ↔ r x' y'))
    (hFunctional : ∀ x y z, Member mem x a → r x y → r x z → Eqv mem y z)
    (hCollect : CollectionInstance mem (ReplacementChoice mem a r)) :
    ∃ b, ∀ z, Member mem z b ↔ ∃ x, Member mem x a ∧ r x z := by
  obtain ⟨b, hSupport, hCover⟩ := hCollect a
  refine ⟨b, fun z => ?_⟩
  constructor
  · rintro ⟨v, hvb, hzv⟩
    obtain ⟨x, hxa, hxv⟩ := hSupport v hvb
    exact ⟨x, raw_member mem hRefl hxa,
      (hInvariant x x v z (hRefl x) (hSymm z v hzv)).mp hxv⟩
  · rintro ⟨x, ⟨u, hua, hxu⟩, hxz⟩
    have huz : r u z := (hInvariant x u z z hxu (hRefl z)).mp hxz
    obtain ⟨v, hvb, _, huv⟩ := hCover u hua ⟨z, hua, huz⟩
    exact ⟨v, hvb, hFunctional u z v (raw_member mem hRefl hua) huz huv⟩

/-- CP yields the singleton-closed INF_lib formulation. The usual Infinity bridge is separate. -/
theorem singleton_closed_of_containers (mem : V → V → Prop) (root : V)
    (hContainers : Containers mem)
    (hPairs : ∀ a b, ∃ p, Pair mem p a b)
    (hRefl : ∀ x, Eqv mem x x)
    (hSymm : ∀ x y, Eqv mem x y → Eqv mem y x)
    (hTrans : ∀ x y z, Eqv mem x y → Eqv mem y z → Eqv mem x z) :
    ∃ v, Member mem root v ∧ ∀ x, Member mem x v →
      ∃ s, Member mem s v ∧ ∀ z, Member mem z s ↔ Eqv mem z x := by
  obtain ⟨v, hRootV, hTransV, hPowerV⟩ := hContainers root
  refine ⟨v, raw_member mem hRefl hRootV, ?_⟩
  rintro x ⟨u, huv, hxu⟩
  obtain ⟨s, hs⟩ := hPairs u u
  obtain ⟨w1, hw1v, hw1⟩ := hPowerV u huv
  obtain ⟨w2, hw2v, hw2⟩ := hPowerV w1 hw1v
  have hsw2 : mem s w2 := hw2 s fun z hzs => hw1 z fun t htz =>
    ((((hs z).mp ⟨z, hzs, same_refl mem z⟩).elim id id : Same mem z u) t).mp htz
  refine ⟨s, raw_member mem hRefl (hTransV w2 hw2v s hsw2), fun z => ?_⟩
  constructor
  · intro hzs
    have hzu : Eqv mem z u := ((pair_of_profile mem hRefl hTrans u u s hs z).mp hzs).elim id id
    exact hTrans z u x hzu (hSymm x u hxu)
  · intro hzx
    exact (pair_of_profile mem hRefl hTrans u u s hs z).mpr (Or.inl (hTrans z x u hzx hxu))

#print axioms same_eqv
#print axioms separation_of_instance
#print axioms subD_bound
#print axioms power_of_instances
#print axioms replacement_of_instance
#print axioms singleton_closed_of_containers

end SetTheory.BusyBeaver.ZFC.ProfileAxioms
