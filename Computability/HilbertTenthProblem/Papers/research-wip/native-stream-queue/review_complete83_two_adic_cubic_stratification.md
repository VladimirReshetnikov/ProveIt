# Independent review: exact 2-adic cubic stratification

**PASS, no correction requested.** The quantified local classification, odd-root lifting and low-central exceptional family are sound. This result constrains the 2-primary part of the cubed-scale condition; it does not establish native masks, a whole-source zero, a noncanonical ordinary input or universal83.

## Frozen sources and read scope

I read the entire new author note, helper and receipt as inert files. Their SHA-256 pins are:

- `/tmp/complete83_two_adic_cubic_stratification.md`: `ad55b60eaebf86eb7e82e1d600497f532d764680dc00c274a3c12607b2c7c9d9`.
- Author JSON: `5bb8a7c1ab2fb7c3cd5b6a30619ddefe49d69c5fa500125bd552fe787feaaf5b`.
- Author PY: `35125c23453a82e16bd0b2818038be07040489567d67afdb4c9f2dcce546e115`.

I also read the full frozen `complete83_even_radix_boundary.md` and `complete83_dyadic_zero_offset_exclusion.md`. The fresh reviewer authenticates all three author dependency pins, including `complete83_shared_projection_math.md`. The inherited source-aligned offset theorem, Pell estimates, native pretyping and compiler size bounds are not independently recertified by this local review. No predecessor helper was executed or imported.

## Independent mathematical challenge

For odd `r>=3`, put `p=popcount(r)`, `k=v2(r+1)`, `ell=v2(r+3)` and `eta=v2(r-1)`. The central-binomial factorial identity and the three adjacent ratios give the coefficient valuations

`p, p-k, p+eta-k, p+eta-k-ell`.

For `alpha=v2(X)>=2`, their weighted valuations are consequently

`p, p+alpha-k, p+2alpha+eta-k, p+3alpha+eta-k-ell`.

When `k>=2`, both `eta` and `ell` equal one. Outside `alpha=k`, the minimum is unique and equals the author's formula (2); at equality, factoring out `2^p` gives exactly (3). The displayed normalized coefficients are integers and odd after removing their stated powers of two: `p>=k` follows from the trailing one-bits of `r`.

When `k=1`, the linear and quadratic terms lie strictly above `p`. If `ell=2`, the cubic term also lies above `p`. If `ell>=3`, then `eta=2`, so the cubic term has valuation `p+1-ell+3alpha`. This proves both the unique-minimum formula (4) and the only possible cubic tie `ell=3alpha+1`. In that tie, the lowest `ell` bits of `r` contain `ell-1` ones; hence `p>=3alpha` and all normalized coefficients in (5) are integral with precisely the asserted parity.

For the linear normalized polynomial, the derivative is odd at every integer. For the cubic normalized polynomial it is odd at every odd integer, which is the domain needed. Each has the unique odd class modulo two. For any root modulo `2^n`, evaluating at `z+2^n` changes its value modulo `2^(n+1)` by `2^n` times that odd derivative; all higher Taylor terms vanish modulo `2^(n+1)`. Exactly one of the two lifts therefore succeeds. This proves uniqueness at every precision, not just the tested ones. The separate case `p>=3t+1` is automatically sufficient because the normalized factor is integral.

The low-central dichotomy follows without discarding cancellation. Every nonresonant minimum is at most `p`, so a passing case with `p<3t+1` must be a linear or cubic tie. In the cubic tie,

`3alpha <= p <= 3t` and `alpha>=t`

force `alpha=t`, `p=3t` and `ell=3t+1`. The low bits already account for every one-bit, forcing exactly `r=2^(3t+1)-3`. Conversely the central and cubic weighted terms then have valuation `3t`, with odd normalized units; their sum is even and the other terms have higher valuation. Every odd unit of `X/2^t` therefore passes the threshold in this exceptional family. The local example `t=2,r=125,X=4` is valid.

For an inherited valid compiler zero, the exceptional `R=2r+1=2^(3t+2)-5` contradicts `R>3q+1` whenever the stated direct size inequality holds. The sufficient condition `3t+1<=d` is conservative and sound:

`R <= 2*2^d-5 < 3*2^d+1 <= 3q+1`.

The proof neither substitutes `log2(q)` for `v2(q)` nor derives dyadicness from evenness. The range `t=1` remains outside this note. Also, a liftable odd residue for `X/2^alpha` is not a source construction: `X=2^R-2^u+W`, the odd-primary conditions, and the retained input and transport equations still have to hold simultaneously.

## Fresh independent evidence

The new reviewer uses direct exact binomials and an independently implemented binary carry count for their valuations. Its branch checks use the actual weighted minima; resonance roots are found by exhaustive enumeration of all odd residue classes, rather than by calling or reproducing the author's lift routine. It checked:

- 383 four-coefficient rows, for every odd `3<=r<=767`;
- 42,896 positive cubic evaluations and 171,584 threshold comparisons, with 1,731 low-central passing comparisons;
- 191 linear and three cubic resonances, each exhaustively through ten bits: 1,940 precision checks;
- 384 complete half-binomial versus four-term congruences for small even non-dyadic radices;
- all nine saved author exceptional-family values, reconstructed directly;
- exceptional weighted-valuation patterns for `t=2,...,64` using binary carries only, and 252 sufficient compiler-size inequalities.

The full-polynomial congruence tests corroborate the inherited elementary truncation argument: `q|X` and even `q` imply `2q^3|X^j` for `j>=4`. They do not check every odd-primary source obligation. No large Pell witness, compiled history, complete source DAG or native mask was evaluated. The finite checks support the all-size proof above and are not its replacement.

The fresh checker `/tmp/review_complete83_two_adic_cubic_stratification.py` has SHA-256 `5c2febf5b434d235857463b3cc862a54bc2299ff9135413b0528fba9302dc5bf`. Its receipt `/tmp/review_complete83_two_adic_cubic_stratification.json` has SHA-256 `259e75d1ffca8107a323048713a8559c41082ea9e4f0186bf9848fd43f416520`. Fresh normal and optimized (`-O`) exact replays from `/` both passed before freezing. Only this new reviewer ran; no repository or Git mutation occurred. No new circuit, gate saving, paid lifting operation or unconstrained universal bound is claimed.
