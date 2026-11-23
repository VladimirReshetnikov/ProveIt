# Fermat's two-square theorem in iPRA

Prepared for Vladimir Reshetnikov, November 22, 2026.

## Result

The report gives a fully developed human-readable proof in intuitionistic
primitive recursive arithmetic of

    Prime(p) -> ((exists a,b in N, a^2+b^2=p) <-> (p=2 or p mod 4=1)).

The positive direction has explicit primitive recursive witness functions.
Wilson's theorem supplies a root of -1 modulo p. A finite collision among
p+1 points in an integer square grid then gives a nonzero multiple of p
strictly below 2p, which must equal p.

The proof also establishes a stronger extraction lemma: if n>0 and
t^2+1 is divisible by n, then n is a sum of two squares. A second,
independently described construction uses centered-residue descent with
exactly p iterations.

## Verification status

- **Mathematics:** complete human-readable argument, including the finite
  inverse construction, Wilson proof, bounded pigeonhole proof, integer
  square root, signed arithmetic encoding, explicit witnesses, converse,
  and a quantifier-free induction audit.
- **Python:** executed. Both constructions succeeded on all 1,125 primes
  congruent to 1 modulo 4 through 20,000. All 2,262 primes in that range
  were also checked against an independently enumerated sum-of-squares
  table. Additional independent and boundary checks are recorded below.
- **Lean:** uncompiled executable specification and conditional theorem
  scaffold. Seven arithmetic contracts are stated as an explicit
  unimplemented argument. No implementation of those contracts and no
  new closed object-level iPRA derivation are claimed.
- **Upstream ProveIt:** relevant source interfaces inspected at the pinned
  commit below. The repository reports its arithmetic libraries as kernel
  checked; this task did not rerun their compilation.

No Lean or Lake executable was available in the preparation environment.
The user requested at least a formalization outline; the supplied outline
identifies every required definition, lemma, dependency, and final proof
object, and marks the remaining work explicitly.

## File map

| File or directory | Contents |
| --- | --- |
| fermat_two_squares_ipra.pdf | Compiled, visually inspected mathematical report. |
| fermat_two_squares_ipra.tex | Complete editable LaTeX source with bibliography. |
| python/two_squares.py | Total bounded witness construction, finite table and direct collision scans, grid certificate verifier, independent descent algorithm. |
| python/validate.py | Independent sum-of-squares enumeration, sieve comparison, certificate checks, and exhaustive small-state checks. |
| validation/validation.json | Recorded successful Python validation. |
| validation/examples.json | Exact grid and descent certificates for selected primes. |
| validation/examples.csv | A compact numerical summary of selected examples. |
| figures/grid_p13.pdf and figures/grid_p13.png | Exact grid diagram explaining the collision construction. |
| python/make_figure.py | Rebuild the diagram with Matplotlib. |
| lean/ | Lean 4 program, explicit contracts, conditional assembly, examples, detailed completion plan, and build target. |
| repository_context.md | Current source review, exact object-theory interfaces, and pinned links. |
| source_provenance.json | Paths, source URLs, and blob identifiers for inspected upstream reference files. |
| build_report.sh | Rebuild the PDF with two LaTeX passes. |
| MANIFEST.sha256 | SHA-256 checksums of the packaged files other than the manifest itself. |

## Reproduce the executable checks

Only Python's standard library is required.

    python3 python/two_squares.py 1009
    python3 python/validate.py --limit 20000

The first command prints exact certificates for

    1009 = 15^2 + 28^2.

The second command writes the results into validation/.

The recorded run checked:

| Check | Cases |
| --- | ---: |
| All primes through 20,000 against an independent representation table | 2,262 |
| Odd target-prime grid certificates | 1,125 |
| Odd target-prime descent certificates | 1,125 |
| Primality and integer-square-root cross-checks for n=0,...,1000 | 1,001 |
| Table-based and direct bounded collision scans, all residues for moduli 1,...,80 | 3,240 |
| Every modular root of -1 for moduli 1,...,200 | 98 |
| Every valid signed descent state within the stated bounds for primes at most 101 | 3,772 |

Modular factorials were compared with exact factorials for primes at most
500. Deliberately changed output coordinates were rejected by the grid
certificate verifier. Testing is finite evidence about implementations;
the universal theorem is proved in the report.

## Rebuild the report

    sh build_report.sh

The script requires pdfLaTeX with standard LaTeX packages. It builds the
PDF from the supplied source and the included vector figure. The delivered
PDF was checked after rendering. To recreate the figure, install Matplotlib
and run python3 python/make_figure.py before rebuilding the report.

## Lean completion

The target is Lean v4.32.0. After installing that toolchain:

    cd lean
    lake build
    lake env lean FermatIPRA/Examples.lean

These commands have not been run here. Even if the scaffold builds,
implementing ArithmeticContracts remains necessary. An ordinary Lean Nat
theorem is a separate milestone from constructing a first-order derivation
of type Prf PRAAx [] phi.

The Lean outline uses a different pair-search order and leaves the two
coordinates unsorted. The report and Python main constructor sort them.
Both target the same sum-of-squares specification; they need not return
identical ordered pairs. The Lean scaffold targets the prime theorem.
Python also implements the stronger arbitrary-modulus root-to-squares
lemma, including its perfect-square branch.

## Repository reuse

Inspected repository:
https://github.com/VladimirReshetnikov/ProveIt

Pinned commit:
65b76a5b8aa87ecad4103c2d287eff5660d3c84c

The most useful existing object-theory modules are Core.Pairing
(integer square root), Core.Pigeonhole (explicit PR collision witnesses),
Core.Division, Core.Search, Core.EuclidLemma, Core.Permutation,
Foundations.BoundedFormulas, and the integer identity compiler.
The detailed plan supplies new Wilson and grid arithmetic derivations
and closes the resulting theorem in the ordinary ConciseIPRA interface.

The existing prime predicate in ProveIt is syntactically quantified.
It must stay in a fixed proof context or be translated to a PR
characteristic bit before entering an induction invariant. Likewise,
Lean's higher-order finite helper functions must be specialized to the
concrete PR predicates; no function quantification is introduced into
the first-order object language.

The repository was read without modification.
