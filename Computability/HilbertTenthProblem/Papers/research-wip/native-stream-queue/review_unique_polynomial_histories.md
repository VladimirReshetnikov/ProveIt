# Review of unique polynomial histories

**The written construction passes review on its stated domain, with a repaired executable input-validation defect.** The report gives a fixed number of polynomial witnesses over `N[X,Y]`, a unique complete Boolean-coefficient history, and an exact reduction to nine affine-linear rows using weighted symbol features. This is a useful intermediate representation. It does not improve the ordinary integer universal-polynomial bound of87 operations.

The immutable source is `docs/incoming/unique_polynomial_histories.zip` at commit `060e08a07d8e6a8ad5ab9ff6c1f7465e22e35630`, SHA256 `0f0f52d5c6617a22cdd0820386eb378c700e5f5c36bfee810ae13818137465e4`. The review covers the complete article, all four Python modules, saved examples and the stated source/trust ledger. The [portable checker](review_unique_polynomial_histories.py) pins all18 members and the [receipt](review_unique_polynomial_histories.json) records the executed evidence. The article is a written proof; no proof-assistant formalization was checked.

## Mathematical findings

The ray equation `U+V=S+MV`, with fixed monomials S,M and nonconstant M, is sound over finite nonnegative-coefficient polynomials. Evaluating at(1,1) forces U to have mass1. Along the directed exponent chains, a finite nonnegative flow has exactly one source and one sink, hence `U=SM^h` and `V=S(1+...+M^(h-1))`. Finiteness and coefficient nonnegativity are essential.

For alphabet size s and nonempty input length m, the full compiler has `s^3+s+5` polynomial unknowns and `3s+3` rows. Its two clocks force endpoint/prefix pairs along the right boundary and time axis. Summing spatial rows gives

    XH+V=H+XQ.

Mass synchronizes the two clock lengths. Since `1-X` is a nonzero divisor, the identity fixes the whole transition mask

    H = sum_(0<=t<h) Y^t (1+X+...+X^(m+2t+1)).

The summed vertical rows then force the terminal mask. Nonnegative coefficients give exactly one tile at every source position and one symbol at every terminal position, with no detached support or multiplicity. Only after this step can marginal labels recover actual neighboring triples. The missing blank right-marginal equation follows from the aggregate identity and all nonblank rows. Vertical rows recover the actual quiescent cellular evolution, including both paid blank guards.

The acceptance rows exclude every earlier accepting event and force exactly one accepting cell on the final row. They uniquely determine the horizontal marker J. An earlier row with multiple accepting cells is also excluded; the condition is first acceptance with singleton multiplicity, not merely the first singleton after arbitrary previous accepting events. These facts determine every polynomial in the witness tuple.

Pair-color, symbol-marginal and injective-feature forms have the same complete natural-polynomial zero set. Weighted features do not identify arbitrary multisets; they identify the already unique symbol on each side of an equation. The two aggregate shape rows must remain. Counts are `6+3 ceil(log2(s))` rows for binary features and nine for one weighted feature when s>=2. The review checker independently verifies594 exact affine identities realizing60 feature-system row maps, including offsets and input constants, across sizes1 through5. These are forward row identities; reverse inclusion uses the reviewed occupancy proof.

The article's Turing-machine bridge is a valid radius-one, one-head construction. A head writes and either stays or transfers its state to the indicated neighboring cell; quiescent background remains blank. Acceptance is attached to the unique head. It supplies an effective generic reduction to a fixed universal matrix, but this archive does not instantiate an independently audited numerical universal cellular table.

Exact witness maxima are `deg_Y=h`, `deg_X=m+2h+1`, and total degree `m+3h+1`, attained by D. Total support is `h^2+mh+5h+m+4+j_*`. The article's no-computable-input-only-degree-bound argument correctly reduces such a bound to deciding universal acceptance. A sum of squared polynomial residuals vanishes identically iff every residual does: evaluation over the reals proves this identity fact without changing the witness domain. The resulting expression is quadratic in polynomial unknowns.

For an external horizon bound H, coefficient extraction instead uses

    (s^3+s+5)(m+2H+2)(H+1)

ordinary natural scalar witnesses. This is a bounded family. Neither nine polynomial rows nor a quadratic expression over `N[X,Y]` is an ordinary fixed-arity Diophantine improvement. The signed-kernel ambiguity argument, scalar-clock counterexample, and parsimonious nondeterministic extension are consistent with the stated domains; the nondeterministic compiler is proved in prose, not implemented in this package.

## Reproduced defect and focused repair

The original CA constructor validates accepting symbols by Python set containment, which identifies `1`, `1.0` and `True`. For a two-symbol identity rule, both `accepting={1.0}` and `accepting={True}` pass construction. The compiler then names final witnesses `T_1.0` or `T_True`, while its declared variable list contains `T_1`. Checking the horizon-zero witness fails with a KeyError. Boolean input/rule symbols can cause related name mismatches. This contradicts the executable claim to validate its finite alphabet; it does not contradict the theorem for exact alphabet symbols.

The [checked patch](unique_polynomial_histories_exact_domains.patch) requires exact integers for alphabet size, table-key and output symbols, accepting symbols, input words, polynomial exponent/coefficient constructors, horizon and feature values. Natural witness polynomials now reject Boolean coordinate/coefficient aliases. The repair changes validation only; all mathematical row formulas remain unchanged. Low-level algebra routines remain helpers rather than a general hostile-object validation API.

Original source SHA256 is `1abf1b9a8a670b7b6b93c23a501eb29d55718307524cab52af3a5bdf21c21013`; patched source is `53c95479edfa477e878741d050644227efa898705ff416e54fb45e9368c52ad3`. The checker reproduces both original failures and rejects36 malformed repaired calls. It compares120 valid compiled systems and360 witness/residual cases across marginal, pair, binary and weighted forms; every valid export is unchanged.

## Replays and transfer value

All three author entry points pass independently on the original and repaired source: `verification.py`, `export_quadratic.py`, and `feature_verification.py`. All10 saved JSON exports reproduce semantically, excluding only the explicitly nondeterministic `elapsed_seconds` field.

The original suite checks59,049 ray flows,19,200 binary rule/input/horizon cases,840 multistate cases,16,384 independent tile assignments and373 worked-example mutations/wrong horizons. The feature suite adds7,456 cases checked in both feature forms,367 mutations per form and exact quadratic evaluations. Binary accepting-symbol tests mainly exercise time-zero acceptance; later acceptance relies on multistate cases and the four-step example, as the author explicitly records. These finite checks support the proof rather than establish universality themselves.

The worked four-symbol certificate has73 polynomial witnesses and74 nonzero coefficients. Its marginal quadratic has2,098 unknown monomials and5,082 expanded coordinate terms. Feature compression reduces15 rows to12 or9 but increases the corresponding expansion to2,704 unknown monomials and12,364 terms. Fewer rows therefore give no automatic arithmetic-operation saving.

A promising transferable fact is same-witness symbol-code compression *after* paid unit occupancy. Applying it to packed integers would still require coefficient access, collision/carry bounds, a common time/space scale and a paid input loader. Raw numeric substitution already destroys the simple clock predicate. No missing packing step or single-fold ordinary MRDP theorem is assumed here.

Reproduce from this directory:

```sh
python review_unique_polynomial_histories.py
```

An explicit `--repo /path/to/Proofs` is supported; a removed incoming archive is recovered from its pinned arrival commit. Default mode compares the receipt without modifying it. `--write` regenerates the receipt. Author outputs and repaired sources exist only in temporary copies; the incoming archive is unchanged.

The external context was checked against the authors' [Lohrey–Steinberg paper](https://arxiv.org/abs/0903.0648), which explicitly describes the tiling/subsemimodule route, and [Dong's STACS paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2023.26), whose tractable problem is a *single homogeneous* equation over `N[X]`. That result does not decide the inhomogeneous systems here. The Narendran publisher page was inaccessible behind a JavaScript check during this review; this review does not independently certify historical priority for the combined normal form.
