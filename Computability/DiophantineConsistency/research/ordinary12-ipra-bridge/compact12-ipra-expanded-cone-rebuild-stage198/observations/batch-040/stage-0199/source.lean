import BusyBeaver.ZFC.KQ1Power

/-! Every Form has collection in the quotient of a `QHyp` structure. -/

namespace SetTheory.BusyBeaver.ZFC.KQ1Collect

open KQHyp
open Form Profile ProfileCollection ProfileComposition ProfileAxioms
open ProfileSyntax ProfileModel CompositionModel DeepPositiveClosure

universe u
variable {V : Type u}

/-- Matrix satisfaction respects both bisimulation-equivalent inputs. -/
theorem rel_matrix_congr (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (phi : Form) (env : Nat → V)
    {x x' y y' : V} (hxx' : Eqv mem x x') (hyy' : Eqv mem y y') :
    KQ1Model.RelSat mem (scons x (scons y env)) phi ↔
      KQ1Model.RelSat mem (scons x' (scons y' env)) phi := by
  apply KQ1Model.relSat_congr mem witness h phi
  intro n
  cases n with
  | zero => exact hxx'
  | succ n =>
    cases n with
    | zero => exact hyy'
    | succ n => exact h.refl (env n)

/-- The raw instance is always the equality-free translation of an actual Form. -/
theorem translated_instance (mem : V → V → Prop) (h : ModelsGIC mem)
    (phi : Form) (env : Nat → V) :
    CollectionInstance mem
      (fun x y => KQ1Model.RelSat mem (scons x (scons y env)) phi) :=
  instance_of_matrix mem h (KQ1Model.translate phi)
    (KQ1Model.equalityFree_translate phi) env _
    (fun x y => KQ1Model.sat_translate mem phi (scons x (scons y env)))

/-- Full native-equality matrices are covered, with an arbitrary quotient valuation. -/
theorem quotient_collection (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (phi : Form)
    (env : Nat → KQ1Model.Domain mem witness h) :
    CollectionInstance (KQ1Model.quotientMember mem witness h)
      (MatrixRelation (KQ1Model.quotientMember mem witness h) phi env) := by
  let rawEnv := KQ1Separation.liftEnv mem witness h env
  have he : (fun i => KQ1Model.mk mem witness h (rawEnv i)) = env := by
    funext i
    exact KQ1Separation.mk_liftEnv mem witness h env i
  have hSat (x y : V) :
      MatrixRelation (KQ1Model.quotientMember mem witness h) phi env
        (KQ1Model.mk mem witness h x) (KQ1Model.mk mem witness h y) ↔
      KQ1Model.RelSat mem (scons x (scons y rawEnv)) phi := by
    have hs := KQ1Model.sat_quotient mem witness h phi (scons x (scons y rawEnv))
    rwa [KQ1Model.mk_scons, KQ1Model.mk_scons, he] at hs
  intro a
  induction a using Quotient.ind with
  | _ a =>
    obtain ⟨b, hSupport, hCover⟩ := translated_instance mem h.gic phi rawEnv a
    refine ⟨KQ1Model.mk mem witness h b, ?_, ?_⟩
    · intro y hy
      induction y using Quotient.ind with
      | _ y =>
        obtain ⟨v, hvb, hyv⟩ := hy
        obtain ⟨x, hxv⟩ := hSupport v hvb
        refine ⟨KQ1Model.mk mem witness h x, (hSat x y).mpr ?_⟩
        exact (rel_matrix_congr mem witness h phi rawEnv
          (h.refl x)
          (h.symm hyv)).mp hxv
    · intro x hx hSome
      induction x using Quotient.ind with
      | _ x =>
        obtain ⟨u, hua, hxu⟩ := hx
        obtain ⟨y, hxy⟩ := hSome
        obtain ⟨y, rfl⟩ := Quotient.exists_rep y
        have huy := (rel_matrix_congr mem witness h phi rawEnv hxu
          (h.refl y)).mp ((hSat x y).mp hxy)
        obtain ⟨v, hvb, huv⟩ := hCover u hua ⟨y, huy⟩
        refine ⟨KQ1Model.mk mem witness h v,
          raw_member mem (h.refl) hvb, (hSat x v).mpr ?_⟩
        exact (rel_matrix_congr mem witness h phi rawEnv
          (h.symm hxu)
          (h.refl v)).mp huv

/-- This schema includes native Eq, with no EqualityFree premise on phi. -/
theorem quotient_fullGIC (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) :
    ∀ phi env, Sat (KQ1Model.quotientMember mem witness h) env (gicForm phi) := by
  intro phi env
  exact (sat_gicForm _ phi env).mpr (quotient_collection mem witness h phi env)

end SetTheory.BusyBeaver.ZFC.KQ1Collect
