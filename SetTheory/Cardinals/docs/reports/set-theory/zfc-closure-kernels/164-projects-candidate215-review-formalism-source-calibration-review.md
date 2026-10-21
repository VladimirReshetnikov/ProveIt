# Independent source-calibration review of the composed 215-state candidate

## Conclusion

**The composed source has exactly the same all-natural register-program semantics as the reviewed public Permuted210 source.** The source-calibration theorem therefore transfers to the new source without changing the numerical calculus, command equations, proof compiler, raw-code soundness invariant, or cofinal enumeration argument.

The exact candidate source is `encoding-work/composition215/source210.json`, SHA-256 `17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`. The exact native binary table under review has SHA-256 `04b4dbb537306f40f8965ad6a0ee6034e9953f079c233153e9696acdf06c2712`.

## Fresh independent source evidence

The standalone `audit_composed_source_equivalence.py` imports neither the source builder nor the binary runtime. It validates both full binary source trees, then resolves every instruction twice by ordinal subtree intervals and binary-address arithmetic. Its fresh receipt is `k215-composed-source-equivalence.json`.

Every resolved operation/register/target tuple is identical to public Permuted210, including both zero and positive decrement branches. There are 4,751 primitive occurrences, 1,425 decrements, and 6,176 guarded cases. The single literal halt is preserved. The exact shared CFG hash is `eb5cd6a5a800a5a525df30fe54b0fce1388f04761980e30eb85071ba67b435ab`.

An additional fresh execution of the public source auditor's independently implemented structured-stack and binary-address resolvers reached the same equality. This is supplementary to the standalone receipt, rather than the source of its interval implementation.

The source depths differ (47 for the composition, 44 for public Permuted210), but both sources have 202 distinct subtrees, 4,751 leaves, and maximum zero run 6. The changed addresses are precisely why graph equality, rather than tree equality or source-subtree count alone, is the relevant theorem.

## Mathematical transfer

Use the relation that pairs the same primitive ordinal and the same natural register tuple in the two sources. Increment, each decrement outcome, each fixed control jump, and halt have identical effects under this relation. It is therefore a step-for-step bisimulation for all natural register contents, including arbitrary raw candidate payloads and all numerical formula-code aliases. In particular the sources halt equivalently from root ordinal zero and the seed `(4,0,0,0,0,0,0,0,0)`.

The public Permuted210 calibration was reviewed separately in `k216-source-calibration-review.md`. Its soundness invariant requires theoremhood of current/cache/stack codes but no restriction on the additive parameter. The zero work-state seed is safe. Its proof compiler has a strong stack-preserving contract and explicitly handles `I(0,0)=0` by omitting the zero-parameter-setting MP. The command-list cursor includes a successor, while a first candidate is loaded as its raw packed payload. Positive cursors decrease, and successful candidate numbers `P(3,P(Y,P(1,R))) >= Y` are cofinal beyond the actual cutoff 4.

Consequently the new source halts from its seed iff the dominated numerical calculus derives falsity. The inherited finite dominated-row recovery certificate and earlier numerical-calculus/ZFC calibration identify that refutation predicate with existence of a ZFC contradiction proof.

## Binary dependency and final endpoint

The parent investigation's fresh exact-table runtime receipt reports `UNIVERSAL_MATHEMATICAL_PASS`, with 6,176/6,176 primitive cases and no failures. The exact blank trace reaches native state 84 at transition 95,726, head -8, gap 1, registers `(4,0,0,0,0,0,0,0,0)`, and forty spare words of value 1. This review inspected the saved runtime/startup metadata, but does not present those separately executed binary checks as its own source-CFG proof.

With those binary obligations discharged, the source bisimulation and reviewed calibration yield, in ZFC, blank halting of the exact 215-state table iff a ZFC refutation exists, and hence blank nonhalting iff `Con(ZFC)`. The concise TeX proof chain is `k215_source_calibration.tex`. The verification level remains ordinary mathematics plus reproducible finite and quantified symbolic checks, not a new exact-table proof-assistant kernel endpoint.
