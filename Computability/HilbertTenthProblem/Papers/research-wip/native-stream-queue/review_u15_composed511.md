# Independent review of the complete 511-operation U15 composition

**PASS; no unresolved finding.** The complete [composition source](u15_packed_composed_units511.py), [receipt](u15_packed_composed_units511.json), and [proof/API note](u15_packed_composed_units511.md) consistently distinguish the two results: the ungrouped forms preserve the entire parent polynomial; the grouped forms preserve its full supplied integer zero set. The optional degree/cost tradeoff is correctly exposed.

Reviewed source SHA-256:
`234a2fcd12e9049ae8903cb44a5c545a61857eba71e4484a0cf3c572827cfc38`.
The [portable review helper](review_u15_composed511.py) authenticates this source and all three selected immediate dependencies before importing it. It records their full hashes in the [independent receipt](review_u15_composed511.json). This review read the full composition, the current guarded unit helper, both predecessor arithmetic transformations and the complete composition note. The already completed [unit-helper review](review_u15_unit524.md) supplies additional independent coverage of its public degree guard and native cancellation proof.

## Complete arithmetic and comparison interfaces

Independent source traversal confirms every emitted gate is live, every source is topologically closed with distinct names, and every binary addition/subtraction/multiplication is counted. The helper reconstructs each finalizer literally from the current comparison list.

| Interface / mode | Certificate | Finalizer | Complete polynomial | Positive witnesses / comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|
| Raw / ungrouped |293=107M+186A|32=11M+21A|325=118M+207A|51 / 11|1936|
| Raw / grouped SOS |294=108M+186A|29=10M+19A|323=118M+205A|51 / 10|3464|
| Ordinary / ungrouped |431=180M+251A|92=31M+61A|523=211M+312A|87 / 31|1936|
| Ordinary / grouped anchor |437=186M+251A|74=25M+49A|511=211M+300A|87 / 25|4881|

The affine stage preserves all seven literal forms in the 29 edge hats. The review independently expands both source versions to exact integer coefficient vectors, including offsets, and compares them to the actual rule table. Replacing only these certified equal expressions by formal cut symbols proves complete residual/SOS DAG equality between 532 and the ungrouped 523/325 forms. This proof uses no equation, Boolean digit or positivity assumption.

For each grouped interface, the checker independently identifies the parent native comparisons by their literal operands, derives the expected factor list and old indices, and verifies the complete retained-comparison map. Raw has two protected factors; ordinary has six protected factors plus the sole loader checksum. Every original comparison occurs exactly once as either a retained residual or a factor equation. The newly added final comparison is precisely `U=1`.

## Integer unit and finalizer proof

The actual guarded factors are

```
N=d²-(a²+4a+3)c²,
H=T²(V²-y²)+y².
```

Modulo 4, the coefficient of `c²` is 0 or 3, so N cannot have residue 3. The second factor reduces modulo 4 to `y²` or `V²`; it also cannot have residue 3. Thus neither protected integer factor equals -1, independently of positivity, native typing or any other comparison. The finite residue checks cover every residue class; the resulting statement is unbounded.

Each protected factor equals 1 plus its original residual. The sole ordinary checksum factor equals 1 minus its original residual. If their integer product U is 1, every factor is a unit. All protected factors must therefore be 1, which also forces the one unrestricted checksum to 1. The converse is immediate. This argument would not justify absorbing two unrestricted checksum factors, and the actual source does not do so.

Let S be the sum of squares of all retained residuals. The complete grouped polynomials are `S+(U-1)²` for raw and `U(1+S)-1` for ordinary. Both vanish exactly when S=0 and U=1 on integer tuples. For the anchor, integrality and `1+S>=1` force both integer factors of 1 to be 1. Combined with the factor proof, this establishes the same full integer zero set as 532. It does not establish equality of off-zero outputs or equivalence over arbitrary real assignments.

Only the replaced private offset registers must have no other live consumers; other comparison operands, including the loader radix, may still be used elsewhere. The revised companion note states this condition correctly. The literal guards and actual source satisfy it.

## Exact degree evidence

The ungrouped polynomial identity transfers degree 1936. For grouped forms, the authenticated main-norm identity

```
(ac+L)²-(a²+4a+3)c² = 2acL+L²-(4a+3)c²
```

removes the known leading cancellation before upper-degree propagation. The source guards authenticate all definitions used in this substitution. The raw factor degrees are 898 and 834, giving degree 1732 for U and 3464 for `(U-1)²`; the retained S has degree at most1936. Ordinary factor degrees are 12, 78, 332, 726, 898, 834, 65, totaling 2945. Its retained S has degree 1936, so the anchor has upper degree 4881. The source's conservative fixed-parameter dependency analysis shows the nonzero leading certificates are independent of the fixed program numerals.

As a separate lower-bound check, this review evaluates **every coefficient of each complete emitted polynomial** along two affine univariate specializations, modulo 1009 and 1013. It does not replace any norm by a simplified expression during those evaluations. Exact integer convolution uses 64-bit coefficient slots, with an explicit no-carry bound checked before every multiplication. The attained degrees and nonzero leading coefficients are:

| Form | Degree | Leading coefficient mod1009 / mod1013 |
|---|---:|---:|
| Raw ungrouped |1936|967 /477|
| Raw grouped |3464|361 /525|
| Ordinary ungrouped |1936|984 /453|
| Ordinary grouped |4881|257 /187|

The grouped specializations agree with the independently reviewed unit-helper source. These two specializations alone do not prove uniformity over every fixed program tuple; that comes from the guarded symbolic upper bound and its conservative no-fixed-dependency leading certificate. The grouped ledger correctly retains the looser literal bounds 3604 raw and 5019 ordinary with `exact_degree_claimed=False`; the separate certificates prove the refined exact degrees.

## Domains, metadata and API

The coordinate interface is unchanged in all four modes. Raw `L0,R0` are natural, including zero; all other default supplied coordinates are positive. Signed mode accepts exact integers. The inherited ordinary theorem retains four fixed positive program numerals on the effective valid-program slices and has no external horizon. This review does not repeat the entire earlier universality construction or claim that arbitrary positive parameter tuples are valid programs. The separate universal 87-operation benchmark is unchanged.

The immediate parent descriptor correctly names 532 in every mode. Ungrouped packets keep their current ancestor comparison map; grouped packets archive it as `pre_unit_ancestor_comparison_map` and supply current factor and retained-residual maps. The ordinary loader comparison count changes from20 to 15, and those 15 active comparisons occupy the actual loader prefix. The five outer comparisons remain. Historical truth reconstruction and removed-comparison descriptors remain historical; they are not charged live gates or silently retained constraints.

The review verifies exact Boolean switches, complete coordinate dictionaries, exact integer types and canonical metadata. It rejects a float coefficient mutation before evaluating 100-digit integers, malformed active/historical maps, invalid flags and out-of-domain coordinates. Public build/source results are defensive copies. Warm-cache tests on private copies alter each of the three immediate dependencies and the inherited 536 source; all four altered-source accesses reject. The private caches do not bypass source authentication.

## Portable replay and finite scope

The independent receipt records:

- 64 complete modulo 4 cases for each of the two protected factor lemmas;
- 14 exact affine vectors, two full affine/residual/SOS DAG identities and four literal source/finalizer checks;
- four current/historical metadata checks;
- 64 complete parent/finalizer evaluations, including 32 signed tuples, 1,344 original residual checks and 144 factor checks;
- eight full modular polynomial specializations;
- 254 malformed-call rejections, eight defensive-copy checks and four warm dependency checks.

A fresh independent replay matched the complete saved JSON byte for byte. A separate fresh default author replay also passed and matched its saved full-source receipt: 96 complete output identities, 48 signed cases, 2,016 original residual checks, 382 malformed-call rejections and eight copy checks.

The all-value source identities and integer-unit argument establish the mathematical relation. Finite evaluations corroborate the actual emitted source and public API; they do not materialize a complete imported universal zero or astronomical Pell witnesses.

From the maintained artifact directory, with the inherited compiler's Python dependencies available:

```sh
python review_u15_composed511.py \
  --source u15_packed_composed_units511.py \
  --root . \
  --expect review_u15_composed511.json \
  --output review_u15_composed511.fresh.json
python u15_packed_composed_units511.py --root .
```

The helper requires explicit paths and assertions. It has no fixed workspace or temporary path. `--expect` compares the complete saved JSON with exact types before writing the fresh receipt. Immediate source authentication precedes imports; the authenticated compiler checks the deeper inherited lineage.
