# Review: sparse-lattice Diophantine certificates

The complete report and all 16 Python modules have been reviewed, including the duplicate Morita audit (verified byte-identical). The generic sparse-history theorem, paid loader/observer, corrected source interface, diameter barrier, mass-two decision proof, and effective semilinearity argument are sound within their stated domains. One low-level exactness defect was found and repaired separately. Original archives are unchanged. This is a mathematical/source review supported by finite replay, not formal verification or a priority claim.

The portable [checker](review_sparse_lattice_aebfa386e.py) pins the archive and all 49 members before extraction/import, checks the original manifest, applies the [constructor patch](sparse_mass_exact_polynomials.patch) privately, and runs both original and repaired complete author replays. The [receipt](review_sparse_lattice_aebfa386e.json) includes both eighteen-stage results and the independent checks. Both large coefficient-explicit Morita fixtures are regenerated, not merely loaded. The original and patched runs match every stable receipt, every generic fixture, both completed source tables, and the decompressed first-pulse fixtures. The original producer's SHA-256 is `1c35e0104730dfe99c9be4c350b49d66646d8e0dd7c7580b262367f1070d02c8`.

## Finding and repair

**P2, public low-level `Poly` constructor:** `replay/core/sparse_mass.py` uses a frozen dataclass but does not validate its directly supplied terms. `Poly((((),float(2**60)),((0,),-1.0)))` passed to `Builder.constrain` accepts the natural witness `2**60+1`: floating evaluation returns zero although the intended integer residual is −1. Mutable nested term containers are also accepted. The factories used by the high-level history compiler and the JSON polynomial decoder already require exact coefficients. Thus the defect does not refute the compiler theorem or demonstrate acceptance of a false bound-export certificate.

The repair validates immutable tuples, exact integer coefficients and indices, sorted monomials, nonzero coefficients, and distinct sorted terms at construction. Negative indices remain legitimate free-parameter references. Eleven malformed constructor forms are rejected, and valid compiler outputs remain coefficientwise identical. The patch does not certify arbitrary reassignment of builder internals or treat the diagnostic unbound `verify_export` as an intended-input authenticator. `verify_bound_export` regenerates the declared input/table/circuit; the caller must still compare that descriptor with its intended instance.

## Full proof and cost audit

The table input order is `(R,C,L)` and output order `(L,C,R)`. Unit-record expansion charges the numerical conserved mass `M`; large empty gaps are numbers, not omitted cells with unknown dynamics. The shift by the external horizon `T` makes every streamed position natural. Conservation forces the vacuum row to zero and ensures that every represented nonempty incoming site remains nonempty. This closes the otherwise dangerous omission of outputs in empty space.

Both comparison branches, including ties, have unique natural slacks. The weak-minus-strict equality expression is exactly a Boolean equality indicator. Collision counts and within-site ranks use all simultaneous arrivals. Natural row selectors summing to one are genuinely one-hot; the three input moments select a unique supplied row. Conservation makes rank redistribution exhaustive. Sorting by `3x+z` is lexicographic on the proved channel domain, and repeated identical records do not introduce particle identities or nonuniqueness.

For a total table with `S=(K+1)^3` rows, the original exact ledger is

```
V = T[M(S+14)+5M(M−1)],
R = T[17M+5M(M−1)].
```

The `T=0` empty tuple is correctly handled. The explicit witness-height bound includes comparison slacks and large gaps. Endpoint equality adds `2M` affine rows, or a constant rejection for a mass mismatch. The literal monomial evaluator counts coefficient multiplication, every variable occurrence, each residual square and each accumulation; it is neither an optimized arithmetic circuit nor a bit-complexity bound. Restricted tables replace `S` only when every actual query remains in the declared domain, which must include vacuum. Completing a partial local injection does not establish that coverage.

The fractional selector counterexample is valid: a half-vacuum/half-double-mass selector has the same input/output moments. Adding norm-one equations to each nonnegative simplex forces genuine one-hot values, giving the stated `2MT` extra core rows over the nonnegative real orthant. This does not extend to unrestricted real selectors. The review independently checks both sides using exact fractions.

The two free counter positions are polynomial parameters. The loader coefficients remain independent of their values and pay `4+3M(M−1)` variables and rows. The observer pays `4MT+3M` variables and `4MT+2M+T` rows, plus final channel norm rows in the orthant variant. Its semantics are zero detector mass before `T` and exactly one at `T`, rather than a generic first occurrence of mass one after arbitrary earlier values. The source pulse has the requisite stronger behavior.

## Source legality, geometry, and semilinearity

The repaired finite local schemes conserve mass, are an injection and can be completed separately within mass fibers. Unconditional identity completion would duplicate outputs. Reachable legality of the source is necessary: the supplied decrement-at-zero counterexample admits a conservative completion producing a false halt pulse. The report retains this counterexample and does not interpret arbitrary input pairs at internal source states as safe encodings.

I checked the printed plus sign in rule (8.2), page 249 of [Morita–Imai's primary paper](https://www.numdam.org/item/ITA_2001__35_3_239_0.pdf). Subtracting the target opcode is forced by mass conservation and the target encoding; the target increment counter, rather than the irrelevant no-op tag, controls marker routing. The review independently reproduces both affected increment cases. This is a mathematical correction, not an asserted author erratum.

The history and prime encodings in [Morita's 1996 paper](https://www.mobt3ath.com/uplode/book/book-94727.pdf), Theorems 3.1 and 4.1, match the report's interfaces. The preservation of legal progress is an additional invariant argument: guarded transfers terminate, legal prime division consumes complete batches, and quotient/residue routines restore the encoded counter. No universal source with numerical state count is printed in the release. The fully specified seven-state source is doubling, with pulse time `5n²+7n+7`, not a universal machine.

Bounded diameter gives finitely many normalized shapes, followed by an exact translating periodic tail. Anchored observations still require solving the tail's displacement equations. Escaping a chosen bound cannot reject an unrestricted later hit. The no-computable-cutoff conclusion correctly uses that distinction. Finite rings have finite mass sectors and cannot replace the line for all unknown times. An injective global evolution cannot enter a preexisting stationary state/cycle from elsewhere; the escaping pulse retains information and is not global halting.

For mass at most two and a unique zero-weight vacuum, a far pair is a pair of finite-state walkers. The first near encounter is found by minimizing across all cycle phases, stopping before hypothetical post-collision crossings. Every later returning excursion starts within a rule-fixed gap and has rule-fixed bounded duration. Only finitely many near shapes exist. This yields the claimed fixed-rule polynomial-time decision procedure on binary sparse coordinates, including intermediate and anchored word queries, without assuming reversibility.

The semilinearity proof preserves absolute entry position and time. Its `Safe(g,T)` guard uses the last strictly earlier occurrence of each phase, so first entry is exact. Once an entry shape is selected from a finite set, subsequent periods/drifts are constants: the initial unbounded gap never multiplies a new unbounded iteration variable. The resulting timed relation is Presburger; projecting time gives untimed reachability. Effective Presburger/semilinear equivalence is confirmed by [Ginsburg–Spanier, Theorem 1.3](https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf). The package implements proof components and sample CA templates, not arbitrary-rule quantifier elimination. Its post-elimination canonical compiler pays the actual atom and Boolean-circuit sizes. Signed coordinate inputs need the stated unique positive/negative split. Time must be eliminated before the canonical compiler for untimed uniqueness.

The two-unit theorem is a decidable-subclass exclusion. It does not prove three particles suffice, a sharp universal mass, a single-fold universal representation, or a new fixed-arity scalar bound. The five-particle literature statement is only abstract-level background in the release; this review makes no stronger optimality/reversibility attribution.

## Executable evidence and continuation

The complete author replay covers 86,928 dense/sparse dynamics comparisons, coefficientwise independent compiler comparisons, all supplied source audit cases, 93,663 encounter/query arithmetic cases, 6,750 sampled far segments, and the two semilinearity suites (1,697,593 and 837,150 cases). The regenerated `n=2,T=41` source fixture has 257,872 variables and 157,683 residuals, and its full coefficient payload reproduces. These are finite implementation checks, not universal-witness enumeration.

The root helper adds 333 complete history cases over all 36 binary conservative permutations plus a noninjective table; their exact paid counts, witness heights, endpoints and unchanged patched polynomials are checked independently. It also checks malformed constructors, changed bound circuits, the real-orthant counterexample, and the printed source correction. All passed on both full author replays.

```
python review_sparse_lattice_aebfa386e.py \
  --archive /path/to/Sparse_Lattice_Diophantine_Certificates.zip \
  --patch sparse_mass_exact_polynomials.patch --authors \
  --expect review_sparse_lattice_aebfa386e.json
```

Two separately reviewed extensions are now available: [wire projection](sparse_lattice_projection.md) of the finite-horizon compiler, and a [five-witness congruence atom](presburger_congruence_five.md) for the low-mass post-elimination compiler. Their counts are kept separate from this original-report review and from the unchanged universal87-operation ledger.
