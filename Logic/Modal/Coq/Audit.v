(** Public surface and kernel-assumption audit for the Foundation modal port. *)

From FoundationModal Require Import
  Syntax Axioms Kripke Filtration Correspondence FiltrationExtensions Loeb
  StandardTranslation Preservation Undefinability.

Check substitute_comp.
Check satisfies_substitute.
Check valid_K.

(** Complete named schema surface from Foundation/Modal/Axioms.lean. *)
Check Axioms.DiaDuality.
Check Axioms.K.
Check Axioms.M.
Check Axioms.C.
Check (@Axioms.N nat).
Check Axioms.T.
Check Axioms.DiaTc.
Check Axioms.B.
Check Axioms.D.
Check (@Axioms.P nat).
Check Axioms.Four.
Check Axioms.FourN.
Check Axioms.Five.
Check Axioms.Point2.
Check Axioms.WeakPoint2.
Check Axioms.C4.
Check Axioms.CD.
Check Axioms.Tc.
Check Axioms.DiaT.
Check Axioms.Ver.
Check Axioms.Point3.
Check Axioms.WeakPoint3.
Check Axioms.Point4.
Check Axioms.Grz.
Check Axioms.Dum.
Check Axioms.McK.
Check Axioms.L.
Check Axioms.Z.
Check Axioms.Hen.
Check Axioms.Mk.
Check Axioms.H.
Check Axioms.Geach.
Check Axioms.I.

Check coarsest_filtration_truth.
Check coarsest_filtration_truth_at_class.
Check filtered_world_cover_bound.
Check finite_countermodel.
Check modal_finite_model_property.
Check satisfiable_has_finite_model.
Check not_valid_has_finite_countermodel.

Check finest_filtration_truth.
Check finest_filtration_truth_at_class.
Check finest_filtered_frame_cover_bound.
Check finest_preserves_reflexive.
Check finest_preserves_serial.
Check finest_preserves_symmetric.
Check finest_tc_filtration_truth.
Check finest_tc_filtration_truth_at_class.
Check finest_tc_filtered_frame_cover_bound.
Check finest_tc_is_transitive.
Check finest_tc_preserves_preorder.
Check finest_tc_preserves_equivalence.

Check valid_Geach_atom_iff_geach_convergent.
Check valid_T_iff_reflexive.
Check valid_D_iff_serial.
Check valid_B_iff_symmetric.
Check valid_Four_iff_transitive.
Check valid_Five_iff_right_euclidean.
Check valid_Tc_iff_coreflexive.
Check valid_Point2_iff_strong_confluence.
Check valid_Point3_iff_piecewise_strong_connected.

Check valid_Loeb_atom_iff_transitive_cwf.

Check bisimulation_invariance.
Check p_morphism_truth.
Check valid_of_surjective_p_morphism.
Check irreflexivity_not_modally_definable.

Check standard_translation_correct.
Check standard_translation_model_validity.
Check standard_translation_diamond_is_existential.

(** Constructive semantic kernel and preservation results. *)
Print Assumptions substitute_comp.
Print Assumptions satisfies_substitute.
Print Assumptions valid_K.
Print Assumptions valid_T_of_reflexive.
Print Assumptions valid_D_of_serial.
Print Assumptions valid_B_of_symmetric.
Print Assumptions valid_Four_of_transitive.
Print Assumptions valid_Five_of_right_euclidean.
Print Assumptions valid_Tc_of_coreflexive.
Print Assumptions valid_Point2_of_strong_confluence.
Print Assumptions bisimulation_invariance.
Print Assumptions valid_of_surjective_p_morphism.
Print Assumptions irreflexivity_not_modally_definable.
Print Assumptions standard_translation_correct.
Print Assumptions standard_translation_model_validity.

(** Filtration's finite list combinatorics is constructive.  Turning
    arbitrary semantic truth into Boolean data, selecting class
    representatives, and identifying subtype proofs are explicitly audited
    below. *)
Print Assumptions subformulas_trans.
Print Assumptions bool_profiles_complete.
Print Assumptions coarsest_filtration_truth.
Print Assumptions filtered_world_cover_bound.
Print Assumptions finite_countermodel.
Print Assumptions modal_finite_model_property.
Print Assumptions satisfiable_has_finite_model.
Print Assumptions finest_filtration_truth.
Print Assumptions finest_filtered_frame_cover_bound.
Print Assumptions finest_tc_filtration_truth.
Print Assumptions finest_tc_filtered_frame_cover_bound.
Print Assumptions finest_tc_preserves_equivalence.

(** Intentional classical boundary: diamond is defined as [~ box ~], so
    extracting witnesses and classical derived connectives uses excluded
    middle. *)
Print Assumptions satisfies_dia_elim.
Print Assumptions valid_Geach_atom_iff_geach_convergent.
Print Assumptions valid_Point3_iff_piecewise_strong_connected.
Print Assumptions valid_Loeb_atom_iff_transitive_cwf.
Print Assumptions standard_translation_diamond_is_existential.
