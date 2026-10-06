# Report 129: independent exact finite companion

This standard-library Python suite supplements the analytic proof of

    n log(mu) - log a(n)
      = sigma S + (7 sigma/3) S loglog(n)/log(n) + O(S/log(n)).

Its result is **finite exact regression only**. The tests do not prove a uniform
estimate, an asymptotic theorem, an effective onset, a coefficient equivalent,
or the unspecified coefficient of S/log(n). No fitted digits, floating-point
calculations, numerical quadrature, or numerical asymptotic certificates occur.

## Offline replay

Python 3.9 or later, POSIX, no third-party dependencies and no network:

```sh
python3 checks/verify.py --output /tmp/report129-verification-new.json
python3 -O checks/verify.py --output /tmp/report129-verification-O-new.json
python3 checks/negative_tests.py --output /tmp/report129-negative-new.json
python3 -O checks/negative_tests.py --output /tmp/report129-negative-O-new.json
```

Output paths must not already exist. With no output argument the scripts emit
the same deterministic JSON to stdout. Compare the verification outputs with
`../data/verification_results.json` and the adversarial outputs with
`../data/negative_results.json`. Ordinary and optimized Python must produce
byte-identical outputs. The current working directory is immaterial. All
arithmetic guards use explicit exceptions, and remain active under `-O`.
Bytecode generation is disabled.

The closed six-member `checks/` inventory is README.md, evidence.json,
manifest.sha256, negative_tests.py, provenance.json, and verify.py. No additional
members, subdirectories, nonregular files, or symlinks are accepted. The sorted
manifest lists all members except itself. The package's outer integrity inventory
seals this manifest. Replay changes no sealed input. Every requested output in
`checks/`, every existing output file, and every output symlink is refused.
The final create uses `O_EXCL` and `O_NOFOLLOW` where available. Manifests catch
uncoordinated changes; replacing code and all integrity anchors is outside their
security claim. Run trusted code.

## Independence and exact checked ranges

The implementation was written afresh from the analytic formulas. It does not
import, execute, or read any prior checker, producer output, or analytic proof
at runtime. The previous Report 127 README was consulted for scope and packaging
conventions. The supplied proof texts and the prior report's mathematical model
were consulted as mathematical specifications, not implementation libraries.

1. **Exact legal transforms.** For each class, heights p=0..10 and rational
   tilt pairs exp(lambda), exp(eta) in {4/5,1,6/5} give 99 comparisons, 198
   altogether. A direct finite sum over the actual legal drops ell<=p-1
   integrates all bulk durations by their generating function. A separately
   implemented negative-binomial or binomial probability recurrence computes
   the drop CDF. The two legal rows agree exactly. The checks retain b=0,
   L=w+1, the ordinary edge, and the genuine domain of the bulk generating
   function. They do not replace the drop cutoff by b<=p or evaluate an
   unrestricted positive-tilt sum over all b.

2. **Moments, level curves, and roots.** At p=0..5 and those nine tilt pairs,
   an independently implemented degree-three rational bivariate Taylor algebra
   gives mass, Delta, L, Delta^2, Delta L, and L^2. These agree with direct
   fixed-b duration mean/variance formulas in 108 cases. Substituting the
   implicit slope and curvature into the jet verifies
   eta'=-T_lambda/T_eta and
   eta''=-E[(Delta+eta' L)^2]/E[L], with a positive duration derivative and
   nonpositive curvature. These sampled rational points generally lie on
   arbitrary fixed level curves, not on row-one roots. At p=1 exact row-one
   roots and their derivatives are checked separately. At p=1,2,4,8 and
   exp(lambda)=1, 48 rational bisections per class give rigorous root brackets
   in exp(eta), with exact endpoint row inequalities. The bracket widths are
   at most 3/2^48. These low-height brackets do not certify a large-p root
   expansion.

3. **Anchored cancellation.** The independently expanded log R has vanishing
   lambda coefficient, eta coefficient alpha, and lambda^2 coefficient
   alpha D/2. Substitution eta=kappa-D lambda^2/2, followed by subtraction
   at lambda=0, has no monomial of weighted degree below three, with weights
   one for lambda and two for kappa. The genuine joint cumulants retain the
   nonzero displacement-duration covariance. They give D=1,1/2; the different
   duration-conditioned values 1/2,1/6 are checked solely as a warning against
   freezing the clock. Scalar balance 1-r=2A0 is exact in both classes.
   Jets establish finite algebraic cancellation, not a uniform Taylor bound.

4. **Corrected potential and action.** Rational symbolic arithmetic verifies
   (1/2)(1/3)+1=7/6 and the first correction of (3A)^(2/3), namely 7/3.
   The binomial jet through cubic order is returned exactly. A sparse Laurent
   polynomial calculation checks the dual identity
   A/x-(-Ax/g^2+2A/g)=A(1-x/g)^2/x coefficientwise. Seven rational x/g values
   exercise the near/far split; the far samples satisfy gap>=A/(4x).
   The all-x inequality and its uniform error absorption are proved in the
   article, not inferred from these samples. No logarithmic penalty or
   continuum integral is certified by numerical sampling.

5. **Clock and error powers.** Exact rational exponent arithmetic checks H,
   S, theta, k, the anchored-root exponent -1/3, scaled-drift exponent -1/6,
   both martingale failure exponents -1/6, the mesh failure exponent -1/6,
   bad-space exponent 1/2, bad-time exponent 11/12, and the tube margin -1/84.
   The endpoint logarithmic cost and time powers are -3 and -9. These are
   arithmetic checks on estimates whose hypotheses remain analytic inputs.
   Four exact cap examples check ceil(4n/(ceH))+1 and its strict accumulated
   conditional-mean lower bound above 2n on the strip p>=eH/2. The old
   numerator 2 is explicitly rejected by an adversarial test.

6. **Genuine original time.** An elementary label-tree dynamic program and
   a separately implemented boundary-cycle renewal convolution have identical
   complete boundary distributions at every n=0..16 in both classes.
   A third implementation directly enumerates inversion sequences and tests
   their forbidden triple relations for every n=0..7. All terminal counts
   agree. The terminal conditions are c=0 for 759 and c=0,p<=2 for 247.
   First-return countdown enumeration agrees with binomial(w-1,b-1) in 128
   cases, b=1..8,w=1..16. Coefficient prefixes are internal exact computations,
   not independent OEIS data. No finite comparison proves the all-size
   combinatorial correspondence.

7. **Certified floors and exact repair.** A positive 60-term atanh series,
   binary range reduction, and an explicit rational geometric remainder
   enclose the required logarithms. Both scaled endpoints must have the same
   floor and width below 10^(-25). The selected k values are
   256,257,258,512,1024,10000,1000000, with their successors also evaluated:
   12 distinct levels in total. Exact support, endpoints, original durations,
   and the moderate window |ell-alpha b|,|w-alpha b|<=b/8 are checked in 70
   stage/return examples. Up/down bridges use offsets 0, half the gap, and
   gap-1 at every selected level.

   There are 5,750 return-fill tests. These include every residue modulo 2R
   above the sufficient threshold at k=256, and selected larger durations
   at all levels, including an added 10^20. The routine uses run-length
   encoding, m=ceil(U/(L+R)), and exact integer excess distribution. At
   k=256,257,258 the bridges, top returns, staircase descent, and b=0 unit
   drops are assembled into 18 complete repairs, each ending at (2,0) at
   exactly its constructed residual time. The suite does not certify the
   uniform mass lower bound, every height, every residual time, or any
   all-k onset. Those statements belong to the analytic discrete lemmas.

8. **Inverse and moment algebra.** The coefficient-threshold inverse inherits
   the factor 7/3 after division by log(mu); its substitution error is
   polynomially below the retained error scale. Separately, a clearly
   distinguished formal inverse of the deficit has leading denominator
   9 sigma^3 and relative loglog(y)/log(y) correction -1. This latter
   calculation is also a consistency check for the moment saddle. The
   log-saddle equation cancels its loglog(k)/log(k) coefficient exactly:
   d/3-4/9+(7/3)/3=0 gives d=-1. The constant
   log(3/sigma^3) is checked using formal log variables. Consequently the
   recorded moment coefficients are 3,-2, -3, and -1, with the symbolic
   log(3/sigma^3) constant kept unevaluated. No saddle localization, tail
   estimate, differentiation of an unknown remainder, or moment asymptotic
   is certified by these algebra tests.

## Provenance and analytic limitations

The combinatorial source is Nathan Britt and Nicholas Beaton, *Completing the
enumeration of inversion sequences avoiding triples of relations*,
[arXiv:2512.21943v3](https://arxiv.org/html/2512.21943v3), sections 3.8 and 3.9.
This identification comes from the supplied mathematical inputs. The companion
makes no fresh network retrieval, priority, or external fixture claim.

The provenance file identifies the reader-facing Report 129, *The next
logarithmic correction for two inversion sequence classes*, and its unchanged
Report 127 input, *Sharp logarithmic deficit constants for two inversion
sequence classes*. Both are included in this reader bundle. Their mathematical
statements are analytic inputs, not machine-checkable proof certificates. The
outer package seals the included articles; the finite checker does not open
these texts during replay. In particular, it does not establish the uniform
CDF-window comparison, local-root or derivative remainder, concentration
inequalities, genuine-clock moment bounds, martingale estimates, path-tube
probability, integrable potential error, nonlocal-tail estimates, spatial
barrier, shrinking-layer construction, exact-time asymptotic extraction, or
any conclusion about an infinite sequence. It does not estimate sigma from data.

## Adversarial checks

The recorded negative suite contains 54 selected semantic, schema, provenance,
and inventory mutations. Every mutation runs in ordinary and optimized Python,
for 108 rejection tests. A rejected run must exit exactly 1, produce exactly
its designated diagnostic, write no result, and leave its temporary sealed
copy unchanged. Mathematical and schema mutations are resealed before replay,
so the intended algebra or schema rejection cannot be replaced by a trivial
hash mismatch. Selected source mutations exercise legal cutoff, drift sign,
duration variance, anchored cancellation, dual square, first-return count,
original-time renewal, bridge direction, and exact integer filling.

Four immutable clean-copy replays check equal ordinary/optimized result bytes.
Eight output-protection tests refuse a new or existing in-tree output, an
existing external file, and an external symlink in both modes. The negative
result records every case and the clean verification-result hash. This is
selected adversarial coverage, not an exhaustive proof of software correctness.
