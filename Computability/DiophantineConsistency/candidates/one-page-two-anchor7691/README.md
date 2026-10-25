# Complete two-anchor7691 consistency equation

The [standalone equation](equation.tex) and [literal evaluator](polynomial.json)
use fifteen strictly positive integer unknowns,66 binary arithmetic
operations with integer leaves, and exact degree157. The four fixed integers
are regenerated coherently from a7691-field layout with two differently
weighted anchors. Their total minimal raw storage is **180987 bytes**,
26227 fewer than the preceding complemented three-anchor47 tuple's207214.

The complete ordinary [native/P66 proof](../../research/two-anchor-independent/PROOF.md),
with its [finite controller certificate](../../research/two-anchor-independent/certificate.json)
and retained K215/refutation calibration, gives the equivalence formalizable
in ZFC between this equation's lack of positive solutions and Con(ZFC).
This is not a proof that either side holds and is not a new end-to-end
proof-assistant derivation. The15-variable domain and full66-gate template
are retained; the four new constants define a different specialized
polynomial from the preceding page.

## What changes

The radix remains rho=2^47, but B changes from rho^8807 to rho^7691. The
second anchor has coefficient2*2^44 at position2195; the anchor at3296 is
removed. The complete array retains3297 slots with all positions2196..3296
zero. The shared polynomial Psi supplies both the unweighted control
support through Psi(x,1) and the weighted controls through1024*Psi(x,2).
Its36 control positions combine with943 selector positions and two dummy
positions to give981 physical positions.

All four integer recipes change together. MC uses the exact support sum
G943(rho)+Psi(rho,1). MF_source includes the native shift beta exactly once
and the signed872-bit padding telescope

    2^26*rho^6726-rho^6708.

K has the bare exponents30,62,1100,7733 and the full reflected Phi term.
Every coefficient, copy group, anchor and zero tail is checked, including
the weighted2195 coefficient; no old3296 anchor or old2201 bare term is
carried forward.

| Metric | Previous three-anchor47 | Two-anchor7691 |
| --- | ---: | ---: |
| Positive unknowns | 15 | 15 |
| Integer-leaf binary operations | 66 | 66 |
| Exact degree | 157 | 157 |
| Four minimal raw integer byte lengths, total | 207214 | 180987 |
| Complete TeX bytes | 5145 | 5083 |

The full fixed seed, decoder,943 indexed tiles, equation front and font
declarations remain byte-identical to the pinned parent. The source retains
Letter paper,9-point body mathematics and7.7-point seed/footer text.
PDF size, extracted text and visual layout are separate rendering checks;
the source builder does not claim or generate those results. No global
minimality claim is made.

## Ordinary mathematical chain

The complete new proof separately establishes both individually recovered
flags, the two-anchor count lemma, scalar boxes, the global29 carry bound,
all phases and alignment, all17 copy fields, both clauses, padding,
occupation and origin. Its new top-field estimate gives F<q/7 and then the
required2C+F<q/3 margin. It retains the exact actual-rank formula and
ordinary dummy increments throughout the controller argument.

The finite certificate supplies lambda=2122441 and bracket residues
18,6993,1324284 modulo47,7691,lambda. It verifies exact base orders and the
valuation-one lift, discharging the new Pc2 premises. This prime belongs
to the completeness proof and is not a coefficient in the printed equation.
Both positive P66 witness directions are stated in section12 of the proof;
the canonical factor values are N0=N1=Na=Nk=Nt=1 and Ns=Delta.

The unchanged free-port circuit has factor degrees22,18,62,7,2,46. Its
entire degree157 leading form has a coefficient8*beta^92, nonzero for the
new positive beta. The retained exact-degree argument therefore applies
to the new specialization without identifying its polynomial with the
different old specialization.

## Reproduction and exact source boundary

The stdlib [`build.py`](build.py) authenticates the final finite verifier
and certificate by exact SHA-256 before execution or import. It runs the
verifier's read-only check, then consumes its complete model and constants.
When the builder runs under optimization, its verifier subprocess inherits
that optimization level. All checks use explicit exceptions.

The builder independently expands the printed Psi formula at1 and2,
constructs the full3297-entry printed Phi array, and compares every entry
with the verifier's actual array. It reconstructs all four printed integers
and compares them directly with `certify.constants` and with every byte
hash in the accepted certificate. Three corrupted control recipes are
rejected: an unweighted second anchor, restoration of the third anchor,
and using Psi(x,1) in the weighted Phi. The complete old TeX and66-gate graph
are pinned separately; exact finite formula replacements determine every
byte of the new TeX.

The four deterministic gzip files contain minimal unsigned big-endian
integers. [BUILD_AUDIT.json](BUILD_AUDIT.json) records the exact support,
weighted anchors, zero tail, gate/liveness checks and complete bindings.
[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) closes the generated source,
four ports, this README and the builder. Rendering artifacts belong to a
separate page manifest, so PDF compilation does not change the source
bundle's read-only check.

From the repository root:

    python3 -B Computability/DiophantineConsistency/candidates/one-page-two-anchor7691/build.py --build
    python3 -B Computability/DiophantineConsistency/candidates/one-page-two-anchor7691/build.py
    python3 -B -O Computability/DiophantineConsistency/candidates/one-page-two-anchor7691/build.py

Only --build writes generated source and coefficient files; the default
checks are read-only. This builder does not invoke the native compiler,
Lean, TeX or a PDF renderer. Earlier complete pages, coefficient tuples
and historical proof records remain preserved.
