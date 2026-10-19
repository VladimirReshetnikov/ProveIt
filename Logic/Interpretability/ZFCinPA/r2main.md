# Internal derivations translate to validator proofs

The unchanged [`R2Main`](Lean/ZFCinPA/R2Main.lean) translates every internal
Tait derivation over the set-theory language into a validator proof of its
encoded sequent. The theorem works in arbitrary IΣ₂ models and retains
`AxOK T V`: every internal axiom of the source theory must have a validator
proof of its encoding. Its corollary transports internal source-theory
refutations to validator falsity, under that same premise.

The proof uses Π₂ induction on the internal derivation code. All ten rule
cases retain their formula, context and variable conditions, using the
checked negation and quantifier translations. This is a translation of
arbitrary internal derivations, rather than only standard finite proof codes.

The [actual check](results/r2main-verification.json) passes nine named axiom
probes and twelve typed callers, including arbitrary derivation/listing
instances and the contrapositive refutation client. Source and audit took
9.818 and 2.485 seconds, with default proof limits, one thread, 4,096 MiB
and a shared 120-second deadline. All reported axioms are standard Lean
axioms. Three existing source unused-section-variable warnings remain;
the audit has none.

The guard selects 47 exact project prerequisites, eight external boundaries
and Init/Omega from the actual R2Quant result. It preserves the parent
warnings and inherited external-cache scope, without rebuilding dependencies
or claiming a whole-namespace attestation. The
[publication](results/r2main-publication.json) and [history](r2main/history.json.gz)
retain the source/API review, exact binding, guard and logs.

The native theory's `AxOK` proof and the reverse consistency direction are
separate prerequisites of the final binary240 PA equivalence.
