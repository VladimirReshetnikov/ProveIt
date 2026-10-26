# Wave 9 arithmetic proposal review

This review covers the full arrival archives at commit `0c6be9a074`, before
their placement and deduplication. The corresponding collection folders are
60-positive-gap, 65-shared-taps, 66-gap-congruence, and 67-oriented-guards.
The receipt is [data/wave9-review-arithmetic.json](data/wave9-review-arithmetic.json).
Original ZIPs and complete manifest-bearing extracted trees were preserved
in scratch. No proposed circuit was treated as a checked Lean endpoint.

## Nine-variable comparison

The following is the cost/degree frontier **among these four archives**.
Every row has nine strictly positive integer inputs; its natural-coordinate
companion has the same degree and seven additional live operations.

| Package and variant | Positive operations | Natural operations | Exact degree |
|---|---:|---:|---:|
| 66, H2082 simple | 444 | 451 | 1,845,940 |
| 66, H2068 simple | 449 | 456 | 1,834,516 |
| 66, H2057 simple | 451 | 458 | 1,825,540 |
| 65, shared-taps economy | 457 | 464 | 1,738,228 |
| 65, shared-taps primary | 458 | 465 | 1,675,396 |
| 67, order 1 | 475 | 482 | 1,663,788 |
| 66, H2082 refined | 476 | 483 | 1,520,178 |
| 66, H2068 refined | 481 | 488 | 1,510,770 |
| 66, H2057 refined | 483 | 490 | 1,503,378 |
| 67, order 4 | 487 | 494 | 1,494,006 |

Package 60 supplies 465/1,797,796, with a 472-operation natural companion,
on both its coherent compact44 and original31 coefficient slices. It is
dominated on operation count and degree within this comparison, but its
explicit compact-tuple adapter and smaller coefficients remain relevant.
Package 67's baseline 462/1,731,700 is dominated by package 65's primary.
Its orders 0, 2, and 3 are also dominated within this table. Coefficient
storage, proof work, variable count, and operation count are distinct
criteria; the table does not assert a global simplicity minimum.

An independent inert-JSON audit checks all 32 primary positive/natural
circuits in these archives: topology, all arithmetic gates live, exactly
nine input variables, and the declared binary operation breakdown. It also
checks 192 modular instances of the positive-to-natural translation using
independent arbitrary fixed-leaf residues. These modular comparisons are
diagnostics. The exact degree claims depend on the displayed universal
cancellation identities and the replayed exact degree certificates, not
on sampled diagonal evaluations. For package 66 and the unchanged-tail
families, the cancellation-resolved degree formulas were also recomputed
independently from their actual source and threshold exponents.

## Source and proof compatibility

**65, shared taps.** This is the lowest-risk degree improvement of the four
relative to the current split116 formalization. An independent symbolic
expansion of its literal `source_system65.json` agrees on all 22 rows with
the exact old-z source already bound by `SplitCertificate59`. This includes
the transport row; no quotient shift is silently omitted. The two row shears
and all free-carrier ratio/finalizer formulas are unchanged.

The primary replaces 89 source-record requirements by 84 unique kernel
positions. A repeated position stores a coefficient once, and is permitted
only when the **complete polynomial in all four ports** agrees at every
owner. It does not sum colliding records. The supplied full-monomial audit
checks 11,616 requirements, including absent monomials. Kernel degrees are
1384/1739/1641, maximum input weight 116, maximum target 1841, and
convolution height 1873. The economy variant has 86 positions and height
1950. Positivity follows from the quadratic leading coefficient +1 and
strict lower-layer gaps, before any binary-base or weak-cap conclusion.

The checked sparse +1 borrow, low-mask decoding, coefficient bound, generic
reduced-rank population identity, and `FreeCarrierRatio` results are reusable.
The unique *kernel* positions remain distinct after compatible coalescing,
so a new literal extraction certificate can use the existing generic
coefficient machinery. Record ownership need not be promoted to a stronger
global uniqueness hypothesis. Remaining work includes the literal certificate,
parameterized source geometry/ranges, and threshold parity factors. In
particular the economy calibration has a factor 2 in `L` and no input `b`
in `N`; those factors cannot be dropped when copying the old calibration.
Its fixed tuple is the whole original31 tuple. Rebinding a compact tuple
requires a separate coherent native adapter.

**66, gap congruence.** The 444-operation point uses the positive source
changes `P_old=P_new+eta+zeta` and `N_old=N_new+q`. Old zero equations give
`P_old-eta-zeta=E*(c-eta)>0` and `N_old=q^3>q`; hence these are actual
bijections of positive zero sets. Its 85-record source has a new `J*s`
interaction: the historical layout fails and is explicitly rejected. The
delivered H2082 certificate repairs that collision. Its degrees are
1627/1941/1850, height 2082, and the unchanged cheap majorant gives
degree 1,845,940. H2068 instead uses `N_old=N_new+1`. H2057 reflects the
weights and reverses one row: each kernel then has a positive leader, and
the two highest substituted layers tie with coefficient `beta+2`. That
tie is retained in its degree argument.

The cheap variants reuse the checked free-carrier finalizer. The refined
variants use a different seventh-order quotient majorant and radical
scale 2048, with a 703-term defect certificate and separate universal
inequalities. Exact finite identities alone do not prove those inequalities.
The conservative bound 172/4096 is **not** smaller than 1/32; the manuscript
correctly distinguishes that loose estimate from the sharper geometric
bound used for 1/32. Its inherited coefficient-sum typo 1719 versus 1619
is an overestimate, so the stated positivity estimate remains sufficient.
All variants use the coherent original31 tuple.

**60, positive gaps.** Besides `P_old=p+eta+zeta`, this source uses
`tau_old=p+t` and `L_old=S-1`. The norm gives
`tau_old^2=p^2+(eta+zeta)*p+1>p^2`, so the new positive `t` is justified;
the first source equation forces `S=q^2>=4`, justifying the inverse
positive `L`. The 86-record source and weight maximum 100 yield height
2047. Its proof explicitly handles `z_old=z_shifted+1`; recovering the
inverse positive transport quotient uses inherited Pell/source soundness,
not merely a polynomial substitution.

The compact44 composition keeps all four ports together. Its canonical
auxiliary lift proves the extra source coordinate positive by
`(I^2-1)*g_aux=V^2-1>0`, rather than asserting an arbitrary source-tuple
bijection. The finalizer is the current free-carrier one. This is useful
source-adapter evidence, although the claimed compact calibration
`kappa=1182967` is larger than the separately reviewed compact54-sharp
calibration and is not a coefficient-size record.

**67, oriented guards.** The nine-variable source itself is the same
authenticated old-z parent as the current formalization. The new layout
uses weights at most 108 and a global row negation. All three kernel
leaders are positive (2, 2, beta), giving unconditional source positivity
without a layer-gap premise. Its height is 1954. The even base-scale
exponent and threshold without an input `b` implement the stated exact
population calibration; the old specialized split116 constants cannot
simply be reused.

The order -1 finalizer is unchanged. Orders 0--4 replace its majorant by
finite polynomial truncations. Their written proof supplies positive
polynomial error, explicit remainder bounds uniform in arbitrarily large
`i`, and corrections that dominate those remainders. A leading asymptotic
expansion alone would be insufficient. The rational-root and margin-first
argument is otherwise the same: prove `m>0` before reconstructing the old
carrier range or invoking radical separation. Formalizing a higher order
requires these new majorant inequalities and a general radical-scale norm
interface. Its degree-certificate polynomials equal `D^16*F`; their larger
gate counts and degrees are not the primary equation's metrics.

The archive also gives a 42-integer quartic and 36/32-integer monic
projections. Their sign orientation depends on the new cofinal restriction
`w=4u^2`, which proves `|E|>3R+1` before recovering the Pell indices. That
order excludes the negative common-sign branch after `p=R`; invoking the
old positive-source theorem earlier would be circular. Completeness uses
canonical parity witnesses, not every old quartic zero. Its 14-positive
adaptive-modulus equation first proves `q^3 | Y`, then uses the modulus
`4qY`; its gcd argument bounds the surviving factor by 3 and never cancels
the full multiplier without proof. These routes require additional signed
Pell/bootstrap formalization beyond the present nine-variable tail.

## Recommendation and formal boundary

Keep the checked same-polynomial 456-operation power-sharing optimization
as a formal baseline. If selecting from these four, package 65's primary
is the clearest next degree target: the source and cheap finalizer agree
with the checked interfaces, and the new work is concentrated in finite
kernel geometry and numerical word calibration. Package 66's 444-operation
point is the next operation target but adds a source-coordinate proof and
different threshold parity. Package 67 order 4 is the degree alternative
after its majorant inequalities are formalized. This recommendation must
be compared with the other four wave 9 proposals before changing the
overall research target.

No new arithmetic counterexample was found in these four written reductions.
This is a review of their arithmetic delta and inherited interfaces, not
a proof of the native semantic calibration or the internal object-language
ZFC equivalence. In particular finite replay, external standard-natural
equivalence, and an exported proof in the repository's ZFC calculus remain
different claims. The new archive theorems must retain those dependencies.

## Release replay

All four full release replays pass. The companion JSON records 65 successful
commands, with normal and optimized modes kept distinct. All runs use Python
3.12.13 from the existing review environment; copies isolate builders from
the pristine full archive trees. Exact commands, return codes, log hashes,
archive/member manifest hashes, and the initial environment retry are recorded.

- Package 60: all 11 declared mixed-mode stages and all 11 complementary-mode
  stages pass. Its independently authenticated manifest seals 205 files.
- Package 65: the complete normal and optimized root replays pass, including
  whole native tuple reconstruction and all three mathematical components.
  Its manifest seals 178 files.
- Package 66: the 18-stage normal root and all 18 directly optimized stages
  pass. The actual final release has 295 sealed files, 80 retained source
  matches, and 64 byte-identical generated rebuilds. Corruption controls
  reject six mutations in both modes (12 rejected runs), plus the listed
  source/packing and integer threshold/mask mutations.
- Package 67: the 25-stage normal root and all 25 directly optimized stages
  pass, with four additional directly optimized signed checkers and the
  root corruption checks. It has 502 sealed files and 66 byte-identical
  generated rebuilds.

Every pristine archive member matches its original ZIP bytes, and each
manifest covers every file except itself. The full trees have 296, 206,
503, and 179 files respectively for gap congruence, positive gap, oriented
guards, and shared taps.

The oriented release intentionally rejects an optimized *root* invocation.
Its normal root and individual optimized stages are therefore the declared
policy. Its first normal attempt reached the projection checker, whose
nested bare `python` did not use the outer virtual environment and could
not import SymPy. Prepending the unchanged environment's `bin` directory
to `PATH` is the retry; no archive source was patched. The initial failure
is retained as an environment portability observation.
