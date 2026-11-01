import BusyBeaver.ZFC.Code254
import BusyBeaver.ZFC.ProfileCollection

/-!
One concrete adapter from the original numerical bundle theory to the
existing CP/GIC semantic resources: every irreflexive EncBundle model with
a supplied valuation has ProfileCollection.Containers.

The selected instance has (a,b,c) = (2,3,1) and matrix Rel(0,0), whose
encoding is exactly1. Both machine gates hold. The named C/G/vacuity trees
below preserve Codes254.v / Bundle254.v from Jeff's verification of
Mira-Cult's machine, upstream297ab8df7e5de329605c3875b4934643b371a5e3.
The container extraction follows the same finite instance argument as
Comp_Bundle254.TB_CP, with a different harmless matrix and label choice.

No arbitrary-number decoder inversion, GIC-schema adapter, quotient ZF
axioms, enumerator or machine endpoint is proved here. The valuation keeps
the model nonempty explicitly; irreflexivity supplies relative falsity.
-/

namespace SetTheory.BusyBeaver.ZFC.Code254Containers

open Tarski Tarski.NF

def falsity : NF := .rel 0 0
def neg (f : NF) : NF := .imp f falsity
def conj (f g : NF) : NF := neg (.imp f (neg g))
def ex (i : Nat) (f : NF) : NF := NF.exF falsity i f

def namedC (a b c : Nat) : NF :=
  ex b (conj (.all a (.imp (.rel a b)
    (conj (ex c (conj (.all b (.imp (.all c (.imp (.rel c b) (.rel c a))) (.rel b c)))
      (.rel c b)))
      (.all c (.imp (.rel c a) (.rel c b))))))
    (.rel c b))

def namedG (a b c : Nat) (phi : NF) : NF :=
  ex c (conj (.all a (.imp (.rel a b)
    (.all b (.imp phi (ex b (conj phi (.rel b c)))))))
    (.all b (.imp (.rel b c) (ex a phi))))

def namedBundle (a b c : Nat) (phi : NF) : NF :=
  conj (conj (namedC a b c) (namedG a b c phi))
    (conj (.imp (.rel a b) (.all c (.rel a b)))
      (.imp (.eq a b) (.all c (.eq a b))))

/-- Exact syntax, including the use of the matrix code as a binder label. -/
theorem enc_namedBundle (a b : Nat) (phi : NF) :
    Code254.enc (namedBundle a b (Code254.enc phi) phi) =
      Code254.bundle a b (Code254.enc phi) := rfl

theorem botFree_namedBundle (a b c : Nat) (phi : NF) (h : BotFree phi) :
    BotFree (namedBundle a b c phi) := by
  simp [namedBundle, namedC, namedG, conj, neg, ex, falsity, NF.exF, BotFree, h]

/-- A fixed finite formula; no astronomical numeral is evaluated. -/
def carrier : NF := namedBundle 2 3 1 (.rel 0 0)

theorem carrier_enc : Code254.enc carrier = Code254.bundle 2 3 1 :=
  enc_namedBundle 2 3 (.rel 0 0)

/-- The whole selected bundle is an actual axiom of EncBundle. -/
theorem carrier_mem : Code254.EncBundle carrier :=
  ⟨botFree_namedBundle 2 3 1 (.rel 0 0) True.intro,
    2, 3, 1, by decide, by decide, carrier_enc⟩

universe u
variable {V : Type u}

theorem sat_conj (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (f g : NF) :
    Tarski.Sat mem e (conj f g) ↔ Tarski.Sat mem e f ∧ Tarski.Sat mem e g := by
  change ((Tarski.Sat mem e f → Tarski.Sat mem e g → mem (e 0) (e 0)) → mem (e 0) (e 0)) ↔ _
  exact ⟨fun h => ⟨Classical.byContradiction fun hf => hirr _ (h fun h' _ => (hf h').elim),
      Classical.byContradiction fun hg => hirr _ (h fun _ h' => (hg h').elim)⟩,
    fun ⟨hf, hg⟩ h => h hf hg⟩

theorem sat_ex (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (i : Nat) (f : NF) :
    Tarski.Sat mem e (ex i f) ↔ ∃ d, Tarski.Sat mem (update e i d) f :=
  Tarski.sat_exF mem hirr e i f

/-- The C component of this instance gives a container for the object at1. -/
theorem container_at_of_namedC (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (h : Tarski.Sat mem e (namedC 2 3 1)) :
    ∃ v, mem (e 1) v ∧ PositiveClosure.Transitive mem v ∧
      ∀ x, mem x v → ∃ p, mem p v ∧
        ∀ z, PositiveClosure.Sub mem z x → mem z p := by
  obtain ⟨v, hv⟩ := (sat_ex mem hirr e 3 _).mp h
  have hc := (sat_conj mem hirr (update e 3 v) _ _).mp hv
  refine ⟨v, by simpa [Tarski.Sat, update] using hc.2, fun x hx z hz => ?_, fun x hx => ?_⟩
  · let exEnv := update (update e 3 v) 2 x
    have hx' : Tarski.Sat mem exEnv (.rel 2 3) := by simpa [exEnv, Tarski.Sat, update] using hx
    have hparts := (sat_conj mem hirr exEnv _ _).mp (hc.1 x hx')
    have hz' : Tarski.Sat mem (update exEnv 1 z) (.rel 1 2) := by
      simpa [exEnv, Tarski.Sat, update] using hz
    simpa [exEnv, Tarski.Sat, update] using hparts.2 z hz'
  · let exEnv := update (update e 3 v) 2 x
    have hx' : Tarski.Sat mem exEnv (.rel 2 3) := by simpa [exEnv, Tarski.Sat, update] using hx
    have hparts := (sat_conj mem hirr exEnv _ _).mp (hc.1 x hx')
    obtain ⟨p, hp⟩ := (sat_ex mem hirr exEnv 1 _).mp hparts.1
    let epEnv := update exEnv 1 p
    have hpower := (sat_conj mem hirr epEnv _ _).mp hp
    refine ⟨p, by simpa [epEnv, exEnv, Tarski.Sat, update] using hpower.2, fun z hz => ?_⟩
    have hsub : Tarski.Sat mem (update epEnv 3 z)
        (.all 1 (.imp (.rel 1 3) (.rel 1 2))) := by
      intro u hu
      have hu' : mem u z := by simpa [epEnv, exEnv, Tarski.Sat, update] using hu
      simpa [epEnv, exEnv, Tarski.Sat, update] using hz u hu'
    simpa [epEnv, exEnv, Tarski.Sat, update] using hpower.1 z hsub

/-- A genuine nonempty EncBundle model supplies the existing container resource.
The valuation is supplied explicitly; the empty-domain loophole is absent. -/
theorem containers_of_encBundle (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (valuation : Nat → V)
    (hB : ∀ f, Code254.EncBundle f → ∀ e : Nat → V, Tarski.Sat mem e f) :
    ProfileCollection.Containers mem := by
  intro a
  let e := update valuation 1 a
  have hall := (sat_conj mem hirr e _ _).mp (hB carrier carrier_mem e)
  have hC := (sat_conj mem hirr e _ _).mp hall.1
  obtain ⟨v, hav, ht, hp⟩ := container_at_of_namedC mem hirr e hC.1
  exact ⟨v, by simpa [e, update] using hav, ht, hp⟩

end SetTheory.BusyBeaver.ZFC.Code254Containers
