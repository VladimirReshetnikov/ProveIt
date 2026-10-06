# Report127: independent finite exact companion

This self-contained standard-library Python companion supplements the analytic
proofs of the sharp logarithmic constants for A279556 (Class 759) and A279551
(Class 247). It checks finite cases and exact algebra. It does **not** certify
an asymptotic statement, an effective onset, or any analytic proof hypothesis.
There are no floating-point calculations, asymptotic fits, fitted digits,
quadrature, or numerical evaluations of pi in this suite.

## Offline replay

Python 3.9 or later on a POSIX system, no external packages or network access:

```sh
python3 /path/to/checks/verify.py --output /tmp/report127-verification.json
python3 -O /path/to/checks/verify.py --output /tmp/report127-verification-O.json
python3 /path/to/checks/negative_tests.py --output /tmp/report127-negative.json
```

Compare the generated files with `../data/verification_results.json` and
`../data/negative_results.json`. Normal and optimized verification are required
to produce byte-identical JSON. The scripts are independent of the current
working directory. With no output argument they print their result JSON;
with an output argument they print one short completion message. Every guard
uses an explicit exception, rather than Python `assert`. Bytecode generation
is disabled. A requested output path resolving inside `checks/` is refused
before any writes, including a path naming an existing sealed member.

The closed, six-member inventory is README.md, verify.py, negative_tests.py,
evidence.json, provenance.json, and manifest.sha256. There may be no extra
files, subdirectories, symlinks, nonregular files, missing members, or unresealed changes. The
manifest lists every member except itself in sorted order. The report's outer
inventory seals the manifest. Hashes detect accidental or uncoordinated
changes; they cannot protect against replacing code and every anchor together.
Run trusted code. Replays do not modify the checks directory.

## Independent implementation and ranges

The verifier is newly implemented from the supplied mathematical formulas.
It never imports, executes, or reads a producer, previous verifier, previous
output, or source proof during replay. Report126 was consulted for packaging,
scope, and integrity conventions. It was not used as an implementation library.
The evidence file contains fixed claims and coverage requirements to test;
it does not contain the derived row, moment, or repair answers.

1. **Exact legal tilted rows.** Write u=exp(lambda), v=exp(eta). At every
   p=0..14 and every pair
   u in {4/5,1,5/4}, v in {4/5,1,6/5}, a raw finite drop sum retains precisely
   ell<=p-1 and sums the complete original bulk duration by its generating
   function. An independently implemented probability recurrence computes
   the negative-binomial or binomial drop CDF. The raw row and CDF row agree
   exactly in all 135 cases per class. These rational tilts are interior to
   the required duration-generating-function domains. Fixed-b unrestricted
   transform identities are separately checked for b=0..8 at the same nine
   tilt pairs: 81 cases per class. No infinite sum over b is evaluated at a
   positive tilt.

2. **Ordinary and b=0 edges.** The root row has only the ordinary edge. A
   zero-commitment edge has L=1 and Delta=-ell, with no bulk part. The bulk
   original-time row sums to one; the limiting unrestricted boundary masses
   are 2/3 and 5/8. Exact rational roots at p=1,u=5/4 are v=36/19 and v=16/7.
   These low-height identities do not replace a large-height root theorem.

3. **Joint moments and drift derivatives.** A new degree-two bivariate
   Taylor-jet implementation differentiates the raw legal row exactly in
   lambda and eta. Independent fixed-b duration mean/variance formulas and
   the finite legal drop sum give mass, Delta, L, Delta^2, Delta L, and L^2.
   All six agree in 135 cases per class. The implicit level-curve identities
   eta'=-T_lambda/T_eta and
   eta''=-E[(Delta+eta' L)^2]/E[L] are checked by substitution back into the
   jet, with positive duration and nonpositive curvature. Most sampled rows
   are level curves through the sampled point, not row-one roots; the
   derivative identities apply to either fixed level. This distinction
   prevents rational sample tilts from being passed off as critical roots.
   At zero tilt the prefactor and per-b means and all covariance entries are
   checked. The diffusion values are 1 and 1/2, whereas the Schur-complement
   duration-conditioned values per unit time are 1/2 and 1/6. No individual
   duration is replaced by its mean in the row or recurrence checks.

4. **True original duration.** A raw elementary label-tree propagation is
   compared with a completed-cycle renewal convolution at every n=0..22,
   both unrestricted and with boundary-visit height caps 2,4,7: 92 full
   boundary-distribution comparisons per class. The cycle's first-return
   counts come from an independent dynamic countdown of outstanding
   commitments, with the first zero emitted once and never continued as a
   bulk state. These agree with binomial(w-1,b-1) in 144 finite cases
   (b=1..8,w=1..18). Terminal extraction is c=0 for 759 and c=0,p<=2 for 247.
   The result contains the internally recomputed coefficient prefixes and
   SHA-256 summaries of every tested family of boundary distributions.
   These checks do not re-prove the all-size combinatorial interpretation.

5. **Certified staircase floors.** An 80-term positive atanh series, binary
   range reduction, and an exact geometric remainder enclose log(k+1).
   Both scaled rational endpoints must give the same floor and their width
   must be less than 10^(-30). No floating logarithm is used. The selected
   k-values are 256..272 and 512,1024,4096,10000,10^6,10^8, with their
   successors additionally evaluated for step gaps. There are 23 selected
   staircase levels. The frozen anchors include
   p_256=363664, R_256=1420,
   p_100000000=184206807539523654, R_100000000=1842068075.

6. **Arbitrary-height bridges and exact-time repair.** For each class the
   selected levels give 115 stage/return endpoint tests and 138 selected
   up/down bridge tests. All sampled cycles satisfy legal support and the
   explicit moderate window |ell-alpha b|,|w-alpha b|<=b/8. Every integer
   height p=363664..418339 is then checked, including every offset between
   successive p_k for k=256..272: 54,676 entrance/repair bridge assemblies
   per class. The entrance starts with ordinary access to the fixed base;
   descent uses the actual downward stages and legal b=0 unit drops to the
   common terminal (2,0). Full original durations are summed.

   The top-return interval is [L-R,L+R], with L=ell_k+1 and
   R=floor(k log(k+1)). Endpoint inequalities check support and the moderate
   window throughout that interval. For U above the sufficient threshold
   ceil((L^2-R^2)/(2R)), the constructive routine sets m=ceil(U/(L+R)),
   starts with m copies of L-R, and distributes the exact integer excess.
   It stores run lengths, so very large U needs no large path allocation.
   There are 52,414 selected or full-residue fill tests per class, plus the
   filling used in every arbitrary-height assembly. Full residue systems
   modulo 2R are tested at the 17 consecutive small/medium levels; the six
   much larger levels use selected U values. Selected targets include an
   added 10^20 duration. The sufficient threshold's integer inequality is
   checked explicitly. Each of the 54,676 full repairs has an exactly
   checked selected residual time. This is a finite regression suite,
   not enumeration of every U or a certification of an all-k onset or
   uniform mass lower bound.

7. **Sharp constants and continuum algebra.** Six Laurent-polynomial
   identities are checked coefficientwise over the rationals, reducing
   P=pi^2 formally by M^3 P=2D/3: the first integral, Euler equation,
   sigma^3=3P/(2D), 3/sigma^3=2D/P, the dual square, and the convex-potential
   residual. Additional rational specializations check the same formulas,
   the kinetic/potential action coefficients, and the inverse correction
   power lambda^(-4/3). The saddle derivative factor
   (1+2/log x)/3, derivative-growth coefficients 3,-2,-3, and the exact
   H,S,theta exponent relations are checked. The action coefficients use
   the integral identities supplied by the proof; the checker does not
   numerically integrate the minimizer or certify existence, uniqueness,
   integration by parts at singular endpoints, a saddle asymptotic, or an
   inverse-threshold theorem.

## Provenance and scope

The primary combinatorial source is Nathan Britt and Nicholas Beaton,
*Completing the enumeration of inversion sequences avoiding triples of
relations*, arXiv:2512.21943v3, sections 3.8 and 3.9:
<https://arxiv.org/html/2512.21943v3>.
The source is identified from the supplied mathematical notes. This companion
makes no fresh source-inspection, network-retrieval, or OEIS-fixture claim.
Coefficient prefixes are internal exact computations, not independent external
data. Matching an earlier internal computation is not a new source.

provenance.json and fixed verifier anchors bind these supplied proof texts:

- sharp upper: b8e88962f370ffd0d9c8c2826be7e30597f203c5b1af7685ad20c476632a46b8
- sharp lower: 6b2c6fad019d31b7b3f2281d6ecbf157ab8766c78d74a171be036daaf84673ea
- local kernel: 93046a0b03e75e328fd0cff3ae58272b6241784d5471d684e01aaf85017ab3ee
- corollaries: 77d9323ff29bf365bc8da3a3e99b795ac384f8bea7fea86cbfbcce1fde688492

Those documents are not runtime dependencies, and their hashes are provenance
identifiers, not machine-checkable proof certificates. The analytic report
and its separate audits establish the infinite-family statements. In
particular this finite suite does not certify concentration bounds, uniform
near-critical local limits, convergence of derivatives from concavity,
martingale estimates, path-space bounds, exponential tightness, time-space
supersolutions, uniform repair mass estimates, exact-time asymptotic
extraction, the sharp coefficient limit, any coefficient next-order term,
coefficient-ratio asymptotics, derivative-growth asymptotics, or an effective
onset. It does not fit or estimate any sequence constant.

## Adversarial checks and immutability

The negative suite tests 59 selected mathematical, schema, provenance, and
inventory changes in normal and optimized Python. Every rejected run must
exit exactly 1, emit the exact designated diagnostic, write no result, and
leave its sealed temporary copy unchanged. Semantic source/data mutations
are resealed, so a hash mismatch cannot masquerade as the intended algebraic
rejection. Schema cases include duplicate keys, nonfinite JSON, booleans
where integers are required, noncanonical rationals, unknown keys, reduced
coverage, and false analytic scope. Inventory cases include extra or missing
members, a directory, a symlink, a named pipe, and malformed/duplicate/unsorted manifest
entries. Selected semantic mutations target cutoff laws, duration variance,
b=0 clocks, original-time extraction, drift sign, staircase endpoints, repair
sign, log remainder, exact filling, and the sharp/inverse/derivative constants.

Four complete clean-copy replays establish equal normal/optimized result
bytes and unchanged inventories. Two additional tests actively refuse an
in-tree output path. The authoritative negative result records all cases
and the clean-result hash. These are selected adversarial regressions, not
an exhaustive proof of software correctness.
