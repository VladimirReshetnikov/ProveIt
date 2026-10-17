`DirtyReset254.lean` proves the six arbitrary-data starts from intake156,
source49, “Reset synchronization and HOD calibration”. The source49 arrival
is `2447a98214b1c4a3e24e51ee654439fbcfa002d9`; its source snapshot is
`fab89c5d26b81cd2ccab2ee5d213ff23725c7726`. The earlier marked-occurrence
argument is attributed to intake155/source42 through the checked
`EnumStackCount254` module. The original enumerator attribution to Mira-Cult,
Jeff Ketchersid and Andrew James Wade is retained.

The checked endpoint is

```text
n ∈ [0,1,2,4,5,6] →
HaltsFrom (pl=0,np=n,tw=t,ws=stack,d=d,h=h) ↔ C254 F.
```

All four working fields are arbitrary. The theorem uses the actual
`Enum254` operations and candidate scheduler; there is no supplied count,
theoremhood, or stack-safety hypothesis.

The proof first identifies the exact command lists of candidates 0 through
6 and proves the actual earlier-candidate balance `credit 7 = 1`. Candidate
6 is a single AX. Its top and new cache are theorems, and its first eight
stack entries are unconditional logical axiom instances. The next entries
are exactly its old generalized cache, old current formula and old stack,
which form an unrestricted tail. Eight good entries suffice for the checked
candidate 7 credit theorem.

This unconditional AX shield shortens the finite argument. Candidates 4 and 5
contain only DROP or MP and cannot halt; candidates 0 and 1 reach candidate 2
through total commands. Candidate 2's MP clears the cache, so candidate 3's
NIP cannot halt before popping. A generic `halts_run_iff` theorem transports
halting across each actual proved-active finite prefix. No formula-reset
arithmetic or assumption about the popped dirty value is needed.

The omitted counter is checked directly: candidate 3 with cache 1 halts
immediately, with all other fields arbitrary. The audit derives the precise
conditional counterexample to a universal candidate 3 equivalence from
`¬ C254 F`. A separate theorem allows counter3 with cache 0.

Pinned Lean 4.32 passed the source in 0.62 s and the final audit in 0.43 s.
The audit contains 19 axiom reports, 12 generic callers and 3 exact syntax/credit
controls; only `propext`, `Classical.choice` and `Quot.sound` occur. Exact
commands, source/object hashes, source-matched dependency closure and audit
source are in `results/dirty-reset254-verification.json`. Dependencies were
reused from the checked integration160 cache, without a boot or full-module
rebuild.

This formalizes the six-start endpoint. It does not yet formalize source49's
sharper weighted `K(p,n)` calculation, exact branch-sensitive seven-command
endpoint, or generalized dirty-root classifier. It makes no new binary
initializer, HOD, Choice or internal PA claim.

The [joint161-unit integration](results/dirty-reset-integration-verification.json)
freshly checks this module and the umbrella, reusing159 source-matched checked
units. Nine axiom reports and six generic callers pass, including the existing
closed binary/ZF endpoint and Con(ZFC) direction. An independent full source
audit of both Count and Reset is preserved in
[`count-reset-independent-review.json`](results/count-reset-independent-review.json).
