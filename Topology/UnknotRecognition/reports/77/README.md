# Compressed Boundary Certificates

**Heisenberg quotients, an exact double-cover universality criterion, and the sharp g+1 bound.**

Research continuation of `Topology/UnknotRecognition` in Vladimir Reshetnikov's
ProveIt repository. Reference revision:

```
cd984a34c0e06e467f3403576afbe6deeb1b5d11
```

The article is `paper/article.pdf`; its complete, self-contained LaTeX source is
`paper/article.tex`. This package is an additive research deliverable. It does
not patch the maintained recognizer and contains no claimed general
quasi-polynomial unknot-recognition algorithm.

## Principal results

**Exact universality test.** For genus g >= 2, a fixed bank A of nonzero
characters detects every essential separating simple curve by the mod-two
homology of an individual lift in some connected double cover if and only if:

1. X = span(A) is coisotropic: X-perp is contained in X.
2. The interaction graph is connected. Choose a basis from A, join each
   remaining vector to the basis vectors in its binary expansion, and join
   basis vectors with nonzero symplectic pairing.

The graph's components give canonical orthogonal blocks. The test needs
O(m*g^2 + g^3) elementary binary operations, apart from near-linear graph
bookkeeping, for m listed characters. No enumeration of curves or splittings
is needed. `boundary_kernel/cover_bank.py` implements it.

**Optimal bank size.** Exactly g+1 covers are necessary and sufficient in this
fixed-double-cover, individual-lift-homology model. Any Lagrangian basis
lambda_1,...,lambda_g together with its sum is optimal. Taking the entire
standard 2g-element symplectic basis is not universal. The claim is not a
lower bound for adaptive covers, higher-degree covers, or arbitrary algorithms.

**Compressed scalar observer.** A marked genus-g surface word is evaluated in

```
H_g(q) = (Z/q)^(2g) x Z/g,
(x,z)*(y,t) = (x+y, z+t+sum_i x[a_i]*y[b_i]).
```

For q=g the quotient has g^(2g+1) elements, but a value needs only 2g+1 modular
coordinates; neither the group table nor the word is expanded. A power SLP
of encoded size S is evaluated in O(S*g*log^2(g+1)) bit operations. S includes
all exponent bits and node references. Default generator vectors are created
lazily, avoiding an otherwise unnecessary quadratic setup cost.

For a source-verified simple curve traversed once, zero signature is equivalent
to contractibility. A zero homology vector with central residue z != 0 is an
essential separator with complementary genera {z,g-z}.

The finite-quotient principle is **classical Livingston/Pikaart theory**, not a
new discovery here. The report gives full coordinate proofs, a compressed
implementation, a certificate interface, and explicit transport contracts.
Polynomial algorithms for arbitrary compressed surface curves also already
exist (Chambers, Lazarus, de Mesmay, and Parsa). See the article's attribution
section and `SOURCE_AUDIT.md`.

**Safe transport.** The smallest common coordinate modulus in this scalar
model that supports all orientation-preserving marking changes is g for odd
g, and 2g for even g. A Dehn twist sends the narrow-zero word a1^g to a word
with central residue g/2 in even genus. The enlarged quotient prevents that
loss. `TransportPlan` checks a symplectic image tuple once and then transports
cached values in O(g^2*log^2(g+1)) bit operations per value. Algebraic checking
of the tuple does not certify a geometric change of marking.

**Independent bridge.** Degree-two binary Magnus data recover complementary
genus ranks and the edge chains of individual lifted curves. A second,
cellular implementation cross-checks the lift formula. The two lifts must not
be added together: their mod-two sum is zero precisely in the useful case.

## Run the package

Python 3.10 or later is required; the delivered run used CPython 3.13.5.
No third-party Python dependencies, network access, or repository checkout
are needed for these local tests.

```sh
python -m unittest discover -s tests -v
python reproduce.py --output-dir results-rerun
python -m boundary_kernel examples/separator_g3.json --genus 3
python -m boundary_kernel examples/separator_g3_certificate.json --verify
```

`reproduce.py` writes to `results-rerun` by default, leaving the delivered
`results` unchanged. For a checks-only run, add `--skip-benchmark`.
Timing values will vary; the deterministic audit data should match exactly.
The default rerun directory may be overwritten on a subsequent rerun with the
same directory argument. Use a new name to retain every run.

PDF rebuild:

```sh
make pdf
# Or, without make:
cd paper
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

A standard LaTeX installation is needed only for rebuilding the PDF.

## Delivered evidence

The final implementation passes **47 unit tests**. These include exact group
identities, signed and huge binary powers, lazy setup, independent matrix
replay, malformed inputs, source-independent negative examples, transport
failure and repair, and cellular/Magnus comparisons.

The exhaustive audits check all 32,768 subsets of the 15 nonzero genus-two
characters against all ten proper symplectic splittings, agreeing with the
universality criterion in every case. Additional exhaustive tests rule out
all 121 banks of size at most two in genus two and all 41,728 banks of size
at most three in genus three. An audit of 1,100 generated splittings in
genera 2 through 12 checks 259,600 symplectic pairings and 2,200 genus ranks.
These are finite algebra audits; they are not a formal proof of the all-genus
theorems, and not a native knot-diagram corpus.

The paired literal/compressed experiment uses the same scalar group law.
For a 295-byte, 18-rule grammar of expanded length 262,148, final-run medians
were approximately 20.03 microseconds compressed and 489.66 milliseconds
literal. For the 16,664-byte grammar of length 8*2^16384+4, compressed evaluation
was approximately 0.735 milliseconds; no literal run was attempted. These
figures exclude parsing, source construction, and certificate replay.

The comparison with bit-packed binary Magnus evaluation is mixed: the scalar
path was slower at genera 2, 4, and 8, and faster at 16, 32, and 64 on the
supplied relator-based family. The package does not claim a native recognizer
speedup or a universal wall-time win.

## Trust boundary

The algebra API returns only `NONTRIVIAL` or `UNDETECTED`. Its
`simple_curve_consequence` field is explicitly conditional on an external,
source-verified simplicity assertion. A zero value for an arbitrary word does
**not** prove that word contractible. `examples/nonsimple_blind_g2.json` is a
nontrivial word missed by every class-two quotient.

The caller must separately verify the closed orientable surface, marking,
ordered component word, geometric source binding, and simple-once property.
Closed-surface contractibility is not boundary-pattern admissibility.
The original torus observer already has an exact parity test and should not
be replaced with this higher-genus research primitive without an actual need.
See `integration/README.md` for the proposed adapter contract.

## Layout

| Path | Purpose |
|---|---|
| `paper/article.{tex,pdf}` | Full proofs, costs, attribution, experiments, ten research questions |
| `boundary_kernel/kernel.py` | Scalar observer, power SLP, safe marking transport |
| `boundary_kernel/verify.py` | Independent dense-matrix certificate replay |
| `boundary_kernel/binary.py` | Magnus and cellular lift observers |
| `boundary_kernel/cover_bank.py` | Coisotropic interaction criterion |
| `tests/test_kernel.py` | Deterministic unit tests |
| `experiments/` | Exhaustive audits and paired local benchmarks |
| `results/` | Final completed-run records and build audit |
| `examples/` | Replayable observations and counterexamples |
| `integration/README.md` | Source contract, migration safeguards, suggested next work |
| `SOURCE_AUDIT.md` | Repository and literature provenance, inspection limitations |
| `CLAIM_LEDGER.md` | What is proved, classical, conditional, and not implemented |

Original package code and documentation are provided under MIT-0, as stated
in `LICENSE`. Cited third-party papers and repository files are not
redistributed in this package. No font files are included.
