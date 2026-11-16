# Mathematics in iPRA through finite observations

## Main deliverable

Read **ipra_embedding_framework.pdf**. Its complete LaTeX source is
`report.tex` together with the seven files in `paper/`.

The report develops a general first-order iPRA framework and gives concrete
repairs of several interfaces exposed by the ProveIt proof collection.
The source baseline is commit
`27a07921176bccbf630084b959700605783ff4aa`.
This is a targeted mathematical audit, not verification of all 47 packets.

## Mathematical results

- **Finite observations and demand.** Bounded formulas become PR Boolean
  predicates; bounded witness selection is explicit; an adaptive PR run
  transfers local arithmetic contracts using a quantifier-free invariant.
  Prefix contracts compose with an explicit finite maximum. A restricted
  syntactic proof discipline compiles mathematically into iPRA, although an
  automatic compiler is not implemented here.
- **Simple analytic branches with Cauchy coefficients.** A supplied root
  `P(0,y0)=0` and a finite witness separating `P_Y(0,y0)` from zero suffice for
  one ordinary power-series branch. The report gives a finite polynomial
  construction, coefficient names, precision schedules, convergence disk,
  tail and residual bounds, and uniqueness. It does not select singular
  Puiseux branches uniformly.
- **Simultaneous finite-window stability.** Several finite variation bounds
  and exceptional-set counts combine by addition of budgets. A bounded
  search returns a common stable window avoiding all the exceptional sets.
  No global Cauchy modulus is inferred.
- **Hyperelliptic zero count.** For odd-degree rational `f` and nontrivial
  `A,B`, every list of distinct rational zeros of `A(x)+B(x)y` on `y²=f(x)`
  has length at most `degree(A²-fB²)`. Double fibers consume multiplicity two.
  This supplies the fiber-count contract in a specified part of the Siegel
  strategy, conditional on the still-missing quantitative covering theorem.
- **Finite algebra certificates.** Coefficientwise identities showing that
  `D` polynomials span a space containing `1` and closed under multiplication
  by each variable modulo the equations imply at most `D` rational solutions.
  The certificate need not be a Gröbner basis and its basis list need not be
  independent. Certificate construction is an additional obligation.

The sharp example `y²=x³-x+1`, `x(x-1)=0` has exactly
`(0,1), (0,-1), (1,1), (1,-1)` and attains both bounds of four.

## Formalization status

| Component | Status |
|---|---|
| Human mathematical proofs and induction accounting | Included in the report |
| `lean/FiniteCore.lean` | Compiled with Lean 4.32.0; proved bounded-search, energy, endpoint, and contract lemmas |
| `lean/Targets.lean` | Compiled concrete definitions and target propositions; the target propositions are not proved |
| `lean/FiniteBranch.lean` | Compiled Gaussian-rational algorithms and five kernel-checked coefficient examples; general kernel goals uninstantiated |
| `lean/ObjectInterface.lean` | Source-level integration outline using actual ConciseIPRA types; not compiled here |
| Full embedded `Prf PRAAx` derivations for the new analytic and geometric theorems | Not implemented; dependency and invariant plan supplied |
| General Siegel/Faltings, general effective Roth, and outstanding prime-distribution estimates | Not proved |

The axiom reports are in `verification/lean_build.txt`. `FiniteCore` uses
Lean's standard `propext` and `Quot.sound` in several proofs; its contract
composition has no axiom dependencies. The five `FiniteBranch` computation
proofs additionally depend on `Classical.choice` through the native
rational/container infrastructure. They are metatheory examples, not
intuitionistic object-theory derivations. No new axioms or `sorry` proofs
are introduced by these files. A declared goal structure is never treated
as a proof of its fields.

## Reproduce

Python 3, standard library only:

```sh
python3 code/reference.py
```

Lean 4.32.0, standard distribution only for the three standalone files:

```sh
bash lean/build.sh
# or:
LEAN_BIN=/absolute/path/to/lean bash lean/build.sh
```

LaTeX with the usual AMS, Latin Modern, geometry, hyperref, xurl, and table
packages:

```sh
bash build_pdf.sh
```

The PDF build script includes a private-runtime fallback for Debian TeX
installations with installed source files but missing generated formats.
It does not change system files. Build products go in `build/`, which is
excluded from the delivered archive.

## Files

- `report.tex`, `paper/`, and `ipra_embedding_framework.pdf`: complete report.
- `lean/`: compiled finite components, exact target definitions, the analytic
  completion plan, and the separate repository integration outline.
- `code/reference.py`: exact reference computations and finite certificates.
- `verification/`: arithmetic results, Lean output, PDF checks, and precise
  formalization status.
- `provenance/SOURCES.json`: 22 inspected repository files with pinned URLs,
  Git blob IDs, SHA-256 hashes, and external background references.
- `CLAIMS.json`: compact statement, hypothesis, and status inventory.
- `PROVEIT_INTEGRATION.md`: proposed integration location and next milestones.
- `SHA256SUMS.txt`: checksums of the delivered files, excluding itself.

Finite computation verifies examples and implementation behavior. It does
not replace the universal human proofs or the remaining object-theory proofs.
