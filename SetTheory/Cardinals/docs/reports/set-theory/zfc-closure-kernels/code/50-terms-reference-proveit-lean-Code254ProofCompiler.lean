import BusyBeaver.ZFC.Code254Proof
import BusyBeaver.ZFC.Enum254

/-!
A structural compiler from finite C254 proof data to enumeration commands.

`compile` consumes the unindexed `RawProof` data directly. It does not inspect
a proposition-valued derivation or select a witness using Choice. Validation
supplies the exact MP equation and the two bundle freshness conditions; the
existing Enum254 block contracts prove the result by structural induction.

The executable command blocks and their attribution are those of Enum254,
following Mira-Cult's published calculus and proof enumerator. This is an
external finite-data compilation theorem. PA representation, arithmetic
totality and internal proof transformations remain separate obligations.
-/

namespace SetTheory.BusyBeaver.ZFC.Code254ProofCompiler

open Code254 Code254Proof Enum254

/- Closed formula codes can be enormous. Use the pairing lemmas rather than
   evaluating the natural-number expression of an axiom instance. -/
attribute [local irreducible] P

/-- Compile every raw tree. Invalid trees receive no execution guarantee. -/
def compile : RawProof → List Cmd
  | .truth => discard
  | .mp b p q => mpBlock b (compile p) (compile q)
  | .gen a p => genBlock a (compile p)
  | .r1 a b => leaf 1 a b 0 0
  | .r2 a b c => leaf 2 a b c 0
  | .r3 a b c => leaf 3 a b c 0
  | .r4 a b c => leaf 4 a b c 0
  | .r5 a b c => leaf 5 a b c 0
  | .r6 a b => leaf 6 a b 0 0
  | .r7 a b c => leaf 7 a b c 0
  | .r8 a b c u => leaf 8 a b c u
  | .bundle a b c => bundleLeaf a b c

/-- From arbitrary top and saved stack, zero accumulator and cache, a valid
proof's block either halts or returns its conclusion with that stack intact. -/
theorem compile_contract (p : RawProof) : p.valid = true →
    Contract (compile p) p.conclusion := by
  induction p with
  | truth => intro _; exact fun T S => Or.inr (cexec_discard T S)
  | mp b p q ihp ihq =>
      intro hv
      simp only [RawProof.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact mp_contract (ihp hv.1) (hv.2.2 ▸ ihq hv.2.1)
  | gen a p ih => intro hv; exact gen_contract a (ih hv)
  | r1 a b => intro _; exact leaf1 a b
  | r2 a b c => intro _; exact leaf2 a b c
  | r3 a b c => intro _; exact leaf3 a b c
  | r4 a b c => intro _; exact leaf4 a b c
  | r5 a b c => intro _; exact leaf5 a b c
  | r6 a b => intro _; exact leaf6 a b
  | r7 a b c => intro _; exact leaf7 a b c
  | r8 a b c u => intro _; exact leaf8 a b c u
  | bundle a b c =>
      intro hv
      simp only [RawProof.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact bundle_contract a b c hv.1 hv.2

/-- Reset the accumulator/cache, run the compiled block and test its result.
The last three commands are exactly the terminator in Enum254.complete. -/
def refutationWord (p : RawProof) : List Cmd :=
  .ax 0 1 1 0 :: (compile p ++ [.drop 0, .nip 0, .nip 0])

/-- A valid proof of the falsity code gives an explicit command word that
halts from every working state, including arbitrary stack/cache contents. -/
theorem refutation_cexec_none (p : RawProof) (hv : p.valid = true)
    (hf : p.conclusion = F) (w : W) : cexec (refutationWord p) w = none := by
  have hp : Contract (compile p) F := hf ▸ compile_contract p hv
  obtain ⟨t, S, d, h⟩ := w
  rw [refutationWord, cexec_cons_some (cstep_ax 0 1 1 0 t S d h), cexec_append]
  rcases hp (gate (d + 1) (h + 1) 0) (axStack (d + 1) h (h + 1) 0 0 t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only
    rw [cexec_cons_some (cstep_drop 0 F _ 0 0)]
    simp only [Nat.add_zero]
    rw [cexec_cons_some (cstep_nip 0 0 _ 0 0 (by omega))]
    simp only [unP_P', Nat.add_zero]
    exact cexec_cons_none (cstep_nip_one 0 0 _ 0)

/-- The old candidate scheduler eventually executes this particular finite
word, unless it has already halted. The compiler itself uses only data. -/
theorem refutation_halts (p : RawProof) (hv : p.valid = true)
    (hf : p.conclusion = F) : Enum254.Halts := by
  apply halts_of_cexec (.ax 0 1 1 0) (compile p ++ [.drop 0, .nip 0, .nip 0])
  exact refutation_cexec_none p hv hf

#print axioms compile_contract
#print axioms refutation_cexec_none
#print axioms refutation_halts

end SetTheory.BusyBeaver.ZFC.Code254ProofCompiler
