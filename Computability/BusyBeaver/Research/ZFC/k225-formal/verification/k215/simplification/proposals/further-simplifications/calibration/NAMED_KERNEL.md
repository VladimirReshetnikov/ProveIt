# Decoder-free lower calibration: exact remaining obligation

Status: mathematical design, not a compiled Lean proof. Pin: beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc.

## What is new beyond the existing structural proposal

The existing proposal chooses a named bundle, then uses sat_encode_decode to feed decoded seed_of_bundle. It saves two syntactic round-trip inductions, but the lower proof still enters the numerical decoder and returns to named syntax for the matrix.

Instead, normalize the named bundle directly. The required freshness fact is ALREADY proved: Code254GIC.not_free_enc m. Its underlying occurs_lt_enc bound covers bound as well as free labels in the exact named syntax. No new structural induction is required.

Define R(e,a,b,m)(x,y) := Tarski.Sat mem (update (update e a x) b y) m.

The precise new theorem is:

    sat_bundleNF_iff_seed
      (mem : V → V → Prop) (e : Nat → V)
      (a b k : Nat) (m : NF)
      (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
      (hfresh : ¬ NF.Free k m) :
      Tarski.Sat mem e (bundleNF a b k m) ↔
      SeedProp mem (R(e,a,b,m)) (e a).

No irreflexivity hypothesis is needed: bundleNF uses genuine NF.bot. No equality-free hypothesis is needed for semantic normalization. Equality-freeness remains needed separately to prove that its interpreted code is derivable.

The theorem is classical, because the bundle expresses its existential container through negated universals. Fresh padding itself is constructive. The overall lower endpoint remains classical and quotient-based; this is not a constructive-equiconsistency claim.

## Three smaller obligations

1. Fresh-matrix environment transport:

       (∀ n, n ≠ k → E n = update (update e a x) b y n) →
       Sat mem E m ↔ R(e,a,b,m)(x,y).

   Apply Tarski.sat_ext; hfresh excludes n=k for every free occurrence. No code or decoder is inspected.

2. Request semantics, for k ≠ b:

       Sat mem E (reqNF b k m) ↔
       ∀ y, Sat mem (update E b y) m →
         ∃ z, Sat mem (update E b z) m ∧ mem z (E k).

   Unfold reqNF, negNF, and Sat, use update_idem, update_same, update_other, then classical quantifier negation. This is the current sat_req normalization without dec, sat_wim, sat_wal, or sat_wn.

3. Closure semantics under the ordinary-role and freshness hypotheses above:

       Sat mem (update e k C) (closNF a b k m) ↔
       ∀ y, mem y C → ∃ x, R(e,a,b,m)(x,y) ∧
         ∀ x', (∀ w, mem w x' → mem w y) →
           ∀ y', R(e,a,b,m)(x',y') →
             ∃ z, R(e,a,b,m)(x',z) ∧ mem z C.

   Use request normalization, fresh-matrix transport, and named-variable update laws. The current seed_of_bundle proof exhibits every environment identity. Prove the equivalence once rather than reconstructing witnesses separately in each direction.

Membership vacuity holds from k ≠ a,b. The outer bundle simplifies to the existence of C satisfying closure and the root request, exactly SeedProp with conjunction order rearranged.

## Final lower adapter

Let pad ψ := NF.all (Code254.enc ψ) ψ, m := pad ψ, and k := Code254.enc m.

- 1 < k follows from enc (all i f) = 4*P(i,enc f)+2.
- EqFree m is definitionally EqFree ψ.
- Freshness of k in m is Code254GIC.not_free_enc m.
- Sat mem e m ↔ Sat mem e ψ follows from freshness of enc ψ in ψ and sat_ext.
- Reverse universal elimination uses e (enc ψ). The explicit valuation precludes an empty-domain inference.

Apply the named-bundle theorem at roles 0,1, then reuse KLower.seedProp_congr with sat_pad. This deletes both sat_encode_decode uses in the first-stage adapter and removes seed_of_bundle, sat_dec_agree, decF_occurs, enc_dec_enc, and eqFree_dec_enc from the LOWER semantic dependency path. Keep enc_bundleNF and th_eqFree to connect the named axioms to the real code calculus.

This does not authorize globally deleting public lemmas. Raw upper soundness still needs the decoder. Module extraction would also be needed to remove import/build dependencies, as opposed to theorem-term dependencies.

## Preserve junk-code and exceptional-role soundness

The new theorem does not replace KSeed222.bundle_of_seed globally. That theorem accepts every raw c with c ≠ a,b, including a=b and code 0. The named theorem intentionally requires a≠b.

KUpper222.zf_refutation_of_c222 and KCode222.c222_sound are unchanged and still quantify over every natural code, not merely encodings or the sparse lower theory:

- dec 0 = T0; literal syntactic preservation at wim(0,0) fails.
- F=1=wel 0 0 decodes to rel 0 0, not genuine bot.
- Semantic falsity of code 1 still requires irreflexivity.
- Equality interpretation and the indiscernibility quotient remain.
- The explicit valuation in c222_complete and the c ≠ a,b gate remain.

An optional shared semantic kernel can parameterize the matrix by a valuation predicate M with invariance off k. Named and decoded adapters supply Sat mem · m and Sat mem · (dec c), using not_free_enc and sat_dec_agree respectively. It could share the ordinary-role proof while retaining the degenerate raw branch. This is a design, not yet a completed formalization.
