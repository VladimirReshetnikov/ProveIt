import BusyBeaver.ZFC.SingletonInfinityCore
import BusyBeaver.ZFC.FiniteSetsCore
import ZF.Zf

/-!
Finite attempts on the least singleton index, without an assumed omega.

The semantic lemmas expose only the particular graph and set-existence
resources used in the argument. They do not assert collection or Separation
for arbitrary semantic relations. Literal first-order formulas and finite-set
graph adapters discharge these resources in the actual CP/GIC quotient.

The backwards attempt argument is adapted from `Std_setrec.v:agree_lemma`,
`att_base`, `exist_lemma` and `closure_thm`, upstream
297ab8df7e5de329605c3875b4934643b371a5e3. Its use with singleton and von
Neumann successor is `Std_setinf.v:or_to_zf_core` in the attributed verification.
-/

namespace SetTheory.BusyBeaver.ZFC.InductiveAttempts

open SingletonInfinity

universe u
variable {V : Type u} {mem : V → V → Prop}

def Agree (app : V → V → V → Prop) (f g z : V) : Prop :=
  ∀ v w, app f z v → app g z w → v = w

def Attempt (B : Base mem) (G : V → V) (app : V → V → V → Prop)
    (N e a f : V) : Prop :=
  (∀ v, app f e v → v = a) ∧
  ∀ z v, mem z N → app f (singleton B z) v →
    ∃ w, app f z w ∧ v = G w

def HasAttempt (B : Base mem) (G : V → V) (app : V → V → V → Prop)
    (N e a z : V) : Prop :=
  ∃ f, Attempt B G app N e a f ∧ ∃ v, app f z v

def Value (B : Base mem) (G : V → V) (app : V → V → V → Prop)
    (N e a z v : V) : Prop :=
  mem z N ∧ ∃ f, Attempt B G app N e a f ∧ app f z v

/-- Only the agreement predicate for these two fixed attempts is separated. -/
theorem agree_of_separator (B : Base mem) (G : V → V) (app : V → V → V → Prop)
    {N e a f g : V} (hN : Index B e N)
    (hSep : ∃ X, ∀ z, mem z X ↔ mem z N ∧ Agree app f g z)
    (hf : Attempt B G app N e a f) (hg : Attempt B G app N e a g) :
    ∀ z, mem z N → Agree app f g z := by
  obtain ⟨X, hX⟩ := hSep
  have heX : mem e X := (hX e).mpr ⟨hN.zero_mem, fun v w hfv hgw =>
    (hf.1 v hfv).trans (hg.1 w hgw).symm⟩
  have hcX : Closed B X := by
    intro z hz
    obtain ⟨hzN, hzAgree⟩ := (hX z).mp hz
    refine (hX (singleton B z)).mpr ⟨hN.closed z hzN, fun v w hfv hgw => ?_⟩
    obtain ⟨v0, hfv0, hv⟩ := hf.2 z v hzN hfv
    obtain ⟨w0, hgw0, hw⟩ := hg.2 z w hzN hgw
    exact hv.trans ((congrArg G (hzAgree v0 w0 hfv0 hgw0)).trans hw.symm)
  exact fun z hz => ((hX z).mp (hN.least X heX hcX z hz)).2

/-- A one-point graph is an attempt because the base has no predecessor. -/
theorem base_attempt (B : Base mem) (G : V → V) (app : V → V → V → Prop)
    (N e a : V) (hNz : ∀ z, mem z N → singleton B z ≠ e)
    (hPoint : ∃ f, ∀ z v, app f z v ↔ z = e ∧ v = a) :
    ∃ f, Attempt B G app N e a f ∧ app f e a := by
  obtain ⟨f, hf⟩ := hPoint
  exact ⟨f, ⟨fun v hv => ((hf e v).mp hv).2,
    fun z v hzN hv => (hNz z hzN ((hf (singleton B z) v).mp hv).1).elim⟩, (hf e a).mpr ⟨rfl, rfl⟩⟩

/-- Adjunction of one new graph point preserves the backwards attempt clauses. -/
theorem extend_attempt (B : Base mem) (G : V → V) (app : V → V → V → Prop)
    {N e a f z v : V} (hNz : ∀ u, mem u N → singleton B u ≠ e)
    (hf : Attempt B G app N e a f) (hzN : mem z N) (hfv : app f z v)
    (hExtend : ∃ g, ∀ u w,
      app g u w ↔ app f u w ∨ (u = singleton B z ∧ w = G v)) :
    ∃ g, Attempt B G app N e a g ∧ app g (singleton B z) (G v) := by
  obtain ⟨g, hg⟩ := hExtend
  refine ⟨g, ⟨?_, ?_⟩, (hg _ _).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · exact fun w hw => ((hg e w).mp hw).elim (hf.1 w) fun hw => (hNz z hzN hw.1.symm).elim
  · intro u w huN hw
    rcases (hg (singleton B u) w).mp hw with hw | ⟨hu, rfl⟩
    · exact (hf.2 u w huN hw).imp fun t ⟨ht, hwt⟩ => ⟨(hg u t).mpr (Or.inl ht), hwt⟩
    · obtain rfl := singleton_injective B hu
      exact ⟨v, (hg _ v).mpr (Or.inl hfv), rfl⟩

/-- Only the fixed attempt-domain-existence predicate is separated here. -/
theorem attempts_exist_of_separator (B : Base mem) (G : V → V)
    (app : V → V → V → Prop) {N e a : V} (hN : Index B e N)
    (hNz : ∀ z, mem z N → singleton B z ≠ e)
    (hPoint : ∃ f, ∀ z v, app f z v ↔ z = e ∧ v = a)
    (hExtend : ∀ f z v, ∃ g, ∀ u w,
      app g u w ↔ app f u w ∨ (u = z ∧ w = v))
    (hSep : ∃ X, ∀ z, mem z X ↔ mem z N ∧ HasAttempt B G app N e a z) :
    ∀ z, mem z N → HasAttempt B G app N e a z := by
  obtain ⟨X, hX⟩ := hSep
  obtain ⟨f0, hf0, hfa⟩ := base_attempt B G app N e a hNz hPoint
  have heX : mem e X := (hX e).mpr ⟨hN.zero_mem, f0, hf0, a, hfa⟩
  have hcX : Closed B X := by
    intro z hz
    obtain ⟨hzN, f, hf, v, hfv⟩ := (hX z).mp hz
    obtain ⟨g, hg, hgv⟩ := extend_attempt B G app hNz hf hzN hfv
      (hExtend f (singleton B z) (G v))
    exact (hX (singleton B z)).mpr ⟨hN.closed z hzN, g, hg, G v, hgv⟩
  exact fun z hz => ((hX z).mp (hN.least X heX hcX z hz)).2

/-- Explicit agreement/existence cuts and one partial-functional image resource
give closure under this fixed G; no semantic all-relations schema is postulated. -/
theorem closure_of_instances (B : Base mem) (G : V → V) (app : V → V → V → Prop)
    {N e a : V} (hN : Index B e N)
    (hNz : ∀ z, mem z N → singleton B z ≠ e)
    (hPoint : ∃ f, ∀ z v, app f z v ↔ z = e ∧ v = a)
    (hExtend : ∀ f z v, ∃ g, ∀ u w,
      app g u w ↔ app f u w ∨ (u = z ∧ w = v))
    (hAgr : ∀ f g, ∃ X, ∀ z, mem z X ↔ mem z N ∧ Agree app f g z)
    (hEx : ∃ X, ∀ z, mem z X ↔ mem z N ∧ HasAttempt B G app N e a z)
    (hImage : (∀ z v w, Value B G app N e a z v →
      Value B G app N e a z w → v = w) →
      ∃ Y, ∀ v, mem v Y ↔ ∃ z, mem z N ∧ Value B G app N e a z v) :
    ∃ Y, mem a Y ∧ ∀ v, mem v Y → mem (G v) Y := by
  have hAgree (f g : V) :=
    agree_of_separator B G app (a := a) hN (hAgr f g)
  have hExists := attempts_exist_of_separator B G app hN hNz hPoint hExtend hEx
  obtain ⟨Y, hY⟩ := hImage fun z v w ⟨hzN, f, hf, hfv⟩ ⟨_, g, hg, hgw⟩ =>
    hAgree f g hf hg z hzN v w hfv hgw
  obtain ⟨f0, hf0, hfa⟩ := base_attempt B G app N e a hNz hPoint
  refine ⟨Y, (hY a).mpr ⟨e, hN.zero_mem, hN.zero_mem, f0, hf0, hfa⟩, fun v hv => ?_⟩
  obtain ⟨z, hzN, _, f, hf, hfv⟩ := (hY v).mp hv
  obtain ⟨g, hg, w, hgw⟩ := hExists (singleton B z) (hN.closed z hzN)
  obtain ⟨v0, hgv0, hw⟩ := hg.2 z w hzN hgw
  have hwG : w = G v := hw.trans (congrArg G (hAgree f g hf hg z hzN v v0 hfv hgv0).symm)
  exact (hY (G v)).mpr ⟨singleton B z, hN.closed z hzN,
    hN.closed z hzN, g, hg, hwG ▸ hgw⟩

/- The templates below are actual first-order formulas. Their two atom builders
are parameters so the independently proved finite-set atoms can be reused. -/

open Form

def attemptForm (appF : Nat → Nat → Nat → Form) (stepF : Nat → Nat → Form)
    (N e a f : Nat) : Form :=
  fAnd
    (fAll (fImp (appF (f + 1) (e + 1) 0) (fEq 0 (a + 1))))
    (fAll (fAll (fAll (fImp
      (fAnd (fMem 2 (N + 3))
        (fAnd (singForm 2 1) (appF (f + 3) 1 0)))
      (fEx (fAnd (appF (f + 4) 3 0) (stepF 0 1)))))))

def agreeForm (appF : Nat → Nat → Nat → Form) (f g z : Nat) : Form :=
  fAll (fAll (fImp
    (fAnd (appF (f + 2) (z + 2) 1) (appF (g + 2) (z + 2) 0)) (fEq 1 0)))

def hasAttemptForm (appF : Nat → Nat → Nat → Form) (stepF : Nat → Nat → Form)
    (N e a z : Nat) : Form :=
  fEx (fAnd (attemptForm appF stepF (N + 1) (e + 1) (a + 1) 0)
    (fEx (appF 1 (z + 2) 0)))

def valueForm (appF : Nat → Nat → Nat → Form) (stepF : Nat → Nat → Form)
    (N e a z v : Nat) : Form :=
  fAnd (fMem z N)
    (fEx (fAnd (attemptForm appF stepF (N + 1) (e + 1) (a + 1) 0)
      (appF 0 (z + 1) (v + 1))))

section Syntax

variable (B : Base mem) (G : V → V) (app : V → V → V → Prop)
    (appF : Nat → Nat → Nat → Form) (stepF : Nat → Nat → Form)
    (hApp : ∀ (env : Nat → V) f x y,
      Sat mem env (appF f x y) ↔ app (env f) (env x) (env y))
    (hStep : ∀ (env : Nat → V) x y,
      Sat mem env (stepF x y) ↔ env y = G (env x))

include hApp hStep in
theorem sat_attemptForm (env : Nat → V) (N e a f : Nat) :
    Sat mem env (attemptForm appF stepF N e a f) ↔
      Attempt B G app (env N) (env e) (env a) (env f) := by
  change ((∀ v, Sat mem (scons v env) (appF (f + 1) (e + 1) 0) → v = env a) ∧
    ∀ z s v, mem z (env N) ∧
      Sat mem (scons v (scons s (scons z env))) (singForm 2 1) ∧
      Sat mem (scons v (scons s (scons z env))) (appF (f + 3) 1 0) →
      ∃ w, Sat mem (scons w (scons v (scons s (scons z env)))) (appF (f + 4) 3 0) ∧
        Sat mem (scons w (scons v (scons s (scons z env)))) (stepF 0 1)) ↔ _
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨fun v hv => h0 v ((hApp _ _ _ _).mpr hv), fun z v hz hv => ?_⟩
    obtain ⟨w, hwApp, hwStep⟩ := hs z (singleton B z) v
      ⟨hz, (sat_singForm B _ 2 1).mpr rfl, (hApp _ _ _ _).mpr hv⟩
    exact ⟨w, (hApp _ _ _ _).mp hwApp, (hStep _ 0 1).mp hwStep⟩
  · rintro ⟨h0, hs⟩
    refine ⟨fun v hv => h0 v ((hApp _ _ _ _).mp hv), ?_⟩
    rintro z s v ⟨hz, hSing, hAppV⟩
    obtain rfl : s = singleton B z := (sat_singForm B _ 2 1).mp hSing
    obtain ⟨w, hwApp, hwStep⟩ := hs z v hz ((hApp _ _ _ _).mp hAppV)
    exact ⟨w, (hApp _ _ _ _).mpr hwApp, (hStep _ 0 1).mpr hwStep⟩

include hApp in
theorem sat_agreeForm (env : Nat → V) (f g z : Nat) :
    Sat mem env (agreeForm appF f g z) ↔ Agree app (env f) (env g) (env z) := by
  change (∀ v w, Sat mem (scons w (scons v env)) (appF (f + 2) (z + 2) 1) ∧
    Sat mem (scons w (scons v env)) (appF (g + 2) (z + 2) 0) → v = w) ↔ _
  exact ⟨fun h v w hv hw => h v w ⟨(hApp _ _ _ _).mpr hv, (hApp _ _ _ _).mpr hw⟩,
    fun h v w ⟨hv, hw⟩ => h v w ((hApp _ _ _ _).mp hv) ((hApp _ _ _ _).mp hw)⟩

include hApp hStep in
theorem sat_hasAttemptForm (env : Nat → V) (N e a z : Nat) :
    Sat mem env (hasAttemptForm appF stepF N e a z) ↔
      HasAttempt B G app (env N) (env e) (env a) (env z) := by
  change (∃ f, Sat mem (scons f env) (attemptForm appF stepF (N + 1) (e + 1) (a + 1) 0) ∧
    ∃ v, Sat mem (scons v (scons f env)) (appF 1 (z + 2) 0)) ↔ _
  exact exists_congr fun _ => and_congr (sat_attemptForm B G app appF stepF hApp hStep _ _ _ _ _)
    (exists_congr fun _ => hApp _ _ _ _)

include hApp hStep in
theorem sat_valueForm (env : Nat → V) (N e a z v : Nat) :
    Sat mem env (valueForm appF stepF N e a z v) ↔
      Value B G app (env N) (env e) (env a) (env z) (env v) := by
  change (mem (env z) (env N) ∧ ∃ f,
    Sat mem (scons f env) (attemptForm appF stepF (N + 1) (e + 1) (a + 1) 0) ∧
      Sat mem (scons f env) (appF 0 (z + 1) (v + 1))) ↔ _
  exact and_congr Iff.rfl (exists_congr fun _ =>
    and_congr (sat_attemptForm B G app appF stepF hApp hStep _ _ _ _ _) (hApp _ _ _ _))

include B hApp in
theorem agreement_separator (N f g : V) :
    ∃ X, ∀ z, mem z X ↔ mem z N ∧ Agree app f g z := by
  obtain ⟨X, hX⟩ := B.sep (agreeForm appF 1 2 0) (scons f (fun _ => g)) N
  exact ⟨X, fun z => (hX z).trans
    (and_congr Iff.rfl (sat_agreeForm app appF hApp _ 1 2 0))⟩

include appF stepF hApp hStep in
theorem existence_separator (N e a : V) :
    ∃ X, ∀ z, mem z X ↔ mem z N ∧ HasAttempt B G app N e a z := by
  obtain ⟨X, hX⟩ := B.sep (hasAttemptForm appF stepF 1 2 3 0)
    (scons N (scons e (fun _ => a))) N
  exact ⟨X, fun z => (hX z).trans (and_congr Iff.rfl
    (sat_hasAttemptForm B G app appF stepF hApp hStep _ 1 2 3 0))⟩

include appF stepF hApp hStep in
theorem value_image
    (hRepl : ∀ (phi : Form) (env : Nat → V), Functional (relOf mem phi env) →
      ∀ A, ∃ Y, ∀ v, mem v Y ↔ ∃ z, mem z A ∧ relOf mem phi env v z)
    (N e a : V)
    (hFunctional : ∀ z v w, Value B G app N e a z v →
      Value B G app N e a z w → v = w) :
    ∃ Y, ∀ v, mem v Y ↔ ∃ z, mem z N ∧ Value B G app N e a z v := by
  let params := scons N (scons e (fun _ => a))
  have hr (z v : V) : relOf mem (valueForm appF stepF 2 3 4 1 0) params v z ↔
      Value B G app N e a z v :=
    sat_valueForm B G app appF stepF hApp hStep (scons v (scons z params)) 2 3 4 1 0
  have hf : Functional (relOf mem (valueForm appF stepF 2 3 4 1 0) params) :=
    fun z v w hv hw => hFunctional z v w ((hr z v).mp hv) ((hr z w).mp hw)
  obtain ⟨Y, hY⟩ := hRepl (valueForm appF stepF 2 3 4 1 0) params hf N
  exact ⟨Y, fun v => (hY v).trans
    (exists_congr (fun z => and_congr Iff.rfl (hr z v)))⟩

include appF stepF hApp hStep in
/-- Definability of the two fixed atoms discharges precisely the three
formula resources, leaving only finite graph existence/extension. -/
theorem closure_of_forms
    (hRepl : ∀ (phi : Form) (env : Nat → V), Functional (relOf mem phi env) →
      ∀ A, ∃ Y, ∀ v, mem v Y ↔ ∃ z, mem z A ∧ relOf mem phi env v z)
    {N e a : V} (hN : Index B e N)
    (hNz : ∀ z, mem z N → singleton B z ≠ e)
    (hPoint : ∃ f, ∀ z v, app f z v ↔ z = e ∧ v = a)
    (hExtend : ∀ f z v, ∃ g, ∀ u w,
      app g u w ↔ app f u w ∨ (u = z ∧ w = v)) :
    ∃ Y, mem a Y ∧ ∀ v, mem v Y → mem (G v) Y := by
  apply closure_of_instances B G app hN hNz hPoint hExtend
  · exact agreement_separator B app appF hApp N
  · exact existence_separator B G app appF stepF hApp hStep N e a
  · exact value_image B G app appF stepF hApp hStep hRepl N e a

end Syntax

/- Fixed finite graphs instantiate the preceding atom templates. -/

def GraphApp (B : FiniteSets.Base mem) (f x y : V) : Prop :=
  mem (FiniteSets.kpair B x y) f

theorem point_graph (B : FiniteSets.Base mem) (e a : V) :
    ∃ f, ∀ z v, GraphApp B f z v ↔ z = e ∧ v = a := by
  refine ⟨singleton B.toBase (FiniteSets.kpair B e a), fun z v => ?_⟩
  change mem (FiniteSets.kpair B z v) (singleton B.toBase (FiniteSets.kpair B e a)) ↔ _
  rw [singleton_spec B.toBase]
  exact ⟨FiniteSets.kpair_inj B, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem extend_graph (B : FiniteSets.Base mem) (f z v : V) :
    ∃ g, ∀ u w, GraphApp B g u w ↔ GraphApp B f u w ∨ (u = z ∧ w = v) := by
  refine ⟨FiniteSets.insert B f (FiniteSets.kpair B z v), fun u w => ?_⟩
  change mem (FiniteSets.kpair B u w) (FiniteSets.insert B f (FiniteSets.kpair B z v)) ↔
    mem (FiniteSets.kpair B u w) f ∨ (u = z ∧ w = v)
  rw [FiniteSets.insert_spec B]
  exact or_congr Iff.rfl ⟨FiniteSets.kpair_inj B, by rintro ⟨rfl, rfl⟩; rfl⟩

/-- Actual finite-set atoms, two Separation cuts and one Replacement image
produce a successor-closed set without any earlier Infinity axiom. -/
theorem successor_closure (B : FiniteSets.Base mem)
    (hRepl : ∀ (phi : Form) (env : Nat → V), Functional (relOf mem phi env) →
      ∀ A, ∃ Y, ∀ v, mem v Y ↔ ∃ z, mem z A ∧ relOf mem phi env v z)
    {N e a : V} (hN : Index B.toBase e N)
    (hNz : ∀ z, mem z N → singleton B.toBase z ≠ e) :
    ∃ Y, mem a Y ∧ ∀ v, mem v Y → mem (FiniteSets.succ B v) Y :=
  closure_of_forms B.toBase (FiniteSets.succ B) (GraphApp B)
    FiniteSets.appForm FiniteSets.succForm
    (FiniteSets.sat_appForm B) (FiniteSets.sat_succForm B) hRepl hN hNz
    (point_graph B e a) (extend_graph B)

/-- The ordinary semantic Infinity axiom from one empty-root singleton container. -/
theorem ordinary_infinity_of_container (B : FiniteSets.Base mem)
    (hRepl : ∀ (phi : Form) (env : Nat → V), Functional (relOf mem phi env) →
      ∀ A, ∃ Y, ∀ v, mem v Y ↔ ∃ z, mem z A ∧ relOf mem phi env v z)
    (e : V) (he : ∀ z, ¬ mem z e) (Y : V) (heY : mem e Y)
    (hY : Closed B.toBase Y) :
    ∃ I, (∃ e0, mem e0 I ∧ ∀ z, ¬ mem z e0) ∧
      ∀ x, mem x I → ∃ sx, mem sx I ∧ ∀ t, mem t sx ↔ mem t x ∨ t = x := by
  obtain ⟨N, hN⟩ := index_of_container B.toBase e Y heY hY
  obtain ⟨I, heI, hI⟩ := successor_closure B hRepl (a := e) hN
    (fun z _ => empty_not_singleton B.toBase e he z)
  exact ⟨I, ⟨e, heI, he⟩, fun x hx =>
    ⟨FiniteSets.succ B x, hI x hx, FiniteSets.succ_spec B x⟩⟩

end SetTheory.BusyBeaver.ZFC.InductiveAttempts
