/- UNCOMPILED integration fragment for KSim.lean, not a standalone module.
Add import BusyBeaver.ZFC.KOracleCut. Replace only the decnz arm of checkEdge: -/

  | .decnz r => decide (Q.length ≤ 48) && decide (r < 9) &&
      KOracleCut.forkTo M FUEL (physOf r) (start Q)
        (tgtConf (breakPath 1 Q) (allOnes (stripPath false 1 Q)) (.plain .none))
        (tgtConf (incPath Q) (allOnes Q) (.plain (.dec (physOf r))))

/- In the semantic decnz case, retain all register, target, and gap reasoning.
After simplifying checkEdge's conjunctions, replace the old split of h0/h1 by:

    obtain ⟨⟨_, hr⟩, hf⟩ := hck

In the zero branch, replace runTo_sound B h0 n ... by:

    KOracleCut.forkTo_sound B hf true n
      (vs := vregs c.registers ++ ext)
      (valid_z hl (by rw [getD_vregs _ _ hr, hv]))

In the positive branch, replace runTo_sound B h1 n ... by:

    KOracleCut.forkTo_sound B hf false n
      (vs := vregs c.registers ++ ext)
      (valid_nz hl (by rw [getD_vregs _ _ hr, hv]; omega))

Each result has the same concrete target used by the existing conc_target rewrite.
The physical register mapping and both original boundedness guards are unchanged.
Full compilation, finite coverage recomputation, and endpoint rebuild remain due.
-/
