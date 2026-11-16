# Applying the ordinal base and step under an internal context

`baseAtCtx` takes an arbitrary model-internal source sequent Γ and internal derivations under Γ of the actual ordinal base for property p, domain(a), and zero(a), and constructs an internal derivation under Γ of p(a).

`stepAtCtx` similarly takes internal derivations under Γ of the actual ordinal step for p, domain(a), domain(b), successor(a,b), and p(a), and constructs an internal derivation under Γ of p(b). The implementation proves the predecessor and successor property placements using internal substitution and the actual fixed ordinal templates. `specializeTwoCtx` and `stepAtTypedCtx` provide the underlying generic two-binder and first-order rules.

The property p, variable indices a and b, and the encoded sequent Γ may all be nonstandard model elements, subject to the displayed internal well-formedness and input-derivation hypotheses. The source theory is any internal Δ₁ theory, and the model is a nonempty candidate-PRA model with IΣ₁ on the induced ordered ring. These are actual typed internal proof-structure constructors, but no fixed uniform arithmetic graph for their proof codes is established here. They do not prove the main arbitrary-property induction sequent or an iPRA theorem.

Run `Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-at-context.sh "$REPO" FRESH_OUTPUT` to recompile both sources into one output against repository-replayed base-application and step-shift objects and prebuilt transitive overlays listed in the checker. It verifies source and immediate dependency hashes and five axiom reports. Passing output `/dev/shm/pa194-internal-induction-at-context-replay`; log `/tmp/pa194-internal-induction-at-context-replay.log`.
