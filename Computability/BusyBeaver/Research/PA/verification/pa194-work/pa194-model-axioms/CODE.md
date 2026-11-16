# Uniform proof-code graphs for shifting separation

`shiftSeparationCodeGraph` and `shiftNegSeparationCodeGraph` are fixed parameter-free Σ₁ arithmetic formulas. Their model-level definability theorems show that they compute `shiftSeparationCode p d` and `shiftNegSeparationCode p d`, respectively, in every covered candidate-PRA + induced-IΣ₁ model. Both input p and proof code d are arbitrary model elements; correctness below requires the stated syntax and proof hypotheses.

For every internally valid arity-one property p, `shiftSeparationProofDirect` turns an internal proof d of its separation root into an actual internal proof of the separation root for `shift SourceL p`; its value is **definitionally equal** to the first graph's output, as verified by `shiftSeparationProofDirect_val`. `shiftNegSeparationProofDirect` and its value theorem do the same for the negated-property separation used by the ordinal derivation. The property and proof codes may be nonstandard, and the internal source theory is any Δ₁ theory.

These are model-level, uniform graph and proof-code results for one helper, not the complete nonstandard ordinal-induction sequent, a general PA proof compiler, or a native iPRA theorem.

Run `Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-shift-code.sh "$REPO" FRESH_OUTPUT` to recompile the source against repository-replayed separation-shift and root-graph objects plus the prebuilt transitive overlays listed in the checker. Source and immediate object hashes are checked; six axiom reports exclude `sorryAx`. Passing output `/dev/shm/pa194-separation-shift-code-replay`; log `/tmp/pa194-separation-shift-code-replay.log`.
