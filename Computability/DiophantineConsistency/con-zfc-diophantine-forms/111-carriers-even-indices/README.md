# Weaker congruences and even Pell indices

Research package for Vladimir Reshetnikov's ProveIt project, 24 October 2026.

**Principal results:** a completely instantiated twelve-integer polynomial of
degree **768**, and a complete direct C222 quartic in **566 integers**. Each
has a proof of equivalence of zero existence to the corresponding inherited
finite-refutation source. Composition with the pinned ordinary source/calculus
calibration proves in ZFC that its absence of integer zeros is equivalent to
Con(ZFC). This is an ordinary mathematical proof, not a new end-to-end
Lean/Rocq or encoded object-ZFC certificate.

Start with **report.pdf**; **report.tex** is its complete editable source.
Every new final equation, every fixed coefficient payload, all new projection
certificates, ordinary proofs, and independent numerical/algebraic checkers
are included. No running machine or proof-predicate oracle occurs in a final
polynomial. The direct branch uses C222, independently of K215 and Jones's
universal polynomial.

## 1. Exact results and comparison

All variables in the following tables range independently over **Z**, with
no implicit positivity restrictions. Degree is total polynomial degree.
Arithmetic operations count every live binary addition, subtraction and
multiplication, including squares and scalar products. Polynomial
abbreviations introduce no new unknowns.

| Twelve-integer construction | Degree | Operations | Exact artifact |
|---|---:|---:|---|
| Pinned rational scalar parent | 1200 | 145 | retained source graph |
| Pinned integral scalar parent | 1456 | 141 | retained source graph |
| Weak carrier, integral | **1040** | **140** | `height12/integral.json` |
| Weak carrier, rational | **816** | **144** | `height12/rational.json` |
| Centered weak carrier | **800** | **147** | `height12/centered.json` |
| Mixed-modulus carrier, integral | **784** | **154** | `crt12/integral.json` |
| Mixed-modulus carrier, rational | **768** | **161** | `crt12/rational.json` |

The 140/1040 and 144/816 points improve both degree and operations relative
to the corresponding parents. The 161/768 point reduces degree by 36% from
the rational parent, at the cost of 16 more binary operations. All five
use the **same complete six-port source34 coefficient tuple**; coefficient
size is not reduced by exchanging tuples. These fixed constants are large:
three masks and the source base have about 1.06 million bits each. Complete
compressed bytes, bit lengths, and SHA-256 bindings are supplied.

| Direct quartic | Variables | Quadratic residuals | Monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Pinned direct parent | 604 | 372 | 9676 | 2445790974704 |
| Seven shared-sum sign pairs | **589** | **371** | **8157** | **2445790974704** |
| Even-index compiler | **566** | **372** | **6431** | **2445790974704** |
| Even-index lower-height alternative | 590 | 396 | 4776 | 964219 |
| Even-index lower-height alternative | 597 | 403 | 4767 | 938267 |

The principal quartic removes 38 variables and 3245 collected monomials from
the matched parent, retaining its degree, residual count, and coefficient
height. It is exactly the sum of the squares of all 372 residuals in
`direct566/support8_default/equation.json`. Its **entire collected polynomial**
is `direct566/support8_default/polynomial.json`.

There is no global simplicity or literature-wide priority claim. Ten-integer
consistency constructions already occur in the source repository; these new
twelve-integer equations improve a degree/cost tradeoff rather than variable
count. Choose the 140-operation equation if arithmetic length matters most,
the degree-768 equation if degree at twelve variables matters most, and the
566-variable equation if degree four is required.

## 2. New mathematical mechanisms

### A weaker congruence suffices at the actual coefficient size

The old carrier forced a projector K to be divisible by H. The new carrier
only forces H to divide K^5. After the unchanged rank and ratio arguments,
this implies H divides an explicit B^5. The actual source base gives the
strict height bound |B|^5 < |H|, forcing B = 0 and recovering exactly the
same source projection. The carrier scale can therefore be made much smaller.

The mixed-modulus refinement places two congruences in

    Phi_D(z) = (z^2 + 3 D^2)(z^3 - 19 D^3),
    D = M H,  M = 2 q^2,
    z = D T + M Kstar + H (v-q^2).

The M^5 part of the divisibility forces M | v-q^2 by a least-valuation
argument; the H part only needs to force H | Kstar^5. This permits Y=qv
in the displayed circuit, then recovers the original odd cubic source
scale before invoking its semantic bounds. The proof explicitly handles
v=0, S=0, c=0, and Q=0 in the necessary order. Completeness fixes its
strong Pell witness before requesting an intersective residue.

### Even indices remove small-ordinate exceptions

Seven source-row identities allow pairs of scalar sign conditions to be
replaced by product signs. The elementary implication is

    r+s=a+b, a>=0, b>=0  =>  (r>=0 and s>=0) iff rs>=0.

Next, each power request m=n^k is certified instead as m^2=n^(2k), with
the original front signs m>=0, n>=1, k>=1 retained. If a main Pell ordinate
had absolute value one, its auxiliary index would have to be odd, contradicting
the required even residue. Thus the index bounds become automatic and twelve
index-sign predicates disappear. The source has 56 predicates after both
changes. A derived t+1 pair advances **two** Pell steps; its literal rows
are changed accordingly. Supporting calls with bases at least two orient
the fifteen seed pairs before remaining base-one calls are interpreted.

The reverse reduction constructs fresh old Pell witnesses from recovered
front arithmetic. It does not assert that old auxiliary coordinates remain
valid after the compiler change.

## 3. Package map

| Path | Contents |
|---|---|
| `report.tex`, `report.pdf` | Complete research article and proof summary |
| `crt12/` | Literal degree-768/784 DAGs, independent checker, full proof and constants |
| `height12/` | Literal degree-800/816/1040 DAGs, independent checker, full proof and constants |
| `direct566/` | 566-variable quartic, two lower-height alternatives, full sparse coefficients, all residuals and inverse maps |
| `direct589/` | Separately verified sign-sharing intermediate and its alternatives |
| `peer/` | Independent mathematical reviews and a second CRT circuit checker |
| `inherited/` | Selected pinned proof/calibration documents and baseline review |
| `SOURCE_LEDGER.json` | Exact provenance, file identities, new-versus-inherited scope |
| `MANIFEST.json` | SHA-256 and byte count for each delivered file other than the manifest itself |
| `verify_all.py` | Portable entry point for every new checker and deterministic rebuild |
| `verification/` | Normal and optimized master receipts, plus PDF quality checks |

### Reading the equations

The twelve-integer JSON graphs are topologically ordered. A node tagged
`variable`, `coefficient`, or `integer` is an input; `add`, `sub`, and `mul`
refer to earlier zero-based node indices. The designated output is the
polynomial. Coefficient nodes are fixed integers from `coefficients/BINDING.json`,
not further quantified coordinates. The words rational and integral name
two auxiliary norm presentations; **both equations have integer coefficients
and unrestricted integer solution domains**. The delivered DAGs contain no
division or square-root operation.

In the direct sparse files, a term `[c, [i, j, ...]]` means the literal
integer coefficient c times the listed coordinate factors, with repeated
indices indicating powers and an empty list indicating a constant. Each
quadratic residual has its own `terms`; the polynomial file is the full
collected sum of their squares. Use the exact coordinate order of the
associated equation file.

## 4. Reproduction

From the extracted package root:

```sh
python3 verify_all.py
python3 -O verify_all.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

All numerical verification uses Python's standard library. Python 3.12 was
used for the delivered receipts. Building the PDF needs an ordinary LaTeX
installation with the packages listed at the beginning of `report.tex`.

The independent checkers import no producer or optimizer. They authenticate
the coefficient bytes, verify full free-ring norm identities and every-gate
attained leading coefficients, check source-row edits and signs, restore
every projected coordinate over the integers, and independently expand every
quartic coefficient. Targeted changes are rejected. The optimized run
establishes that acceptance does not depend on Python `assert` statements.
The master runner also checks the whole-file manifest when present.

The generic odd-index counterexample is included and checked in
`direct566/odd_index_negative_control.json`. It invalidates deleting the
index guards without the parity change. It is expressly **not a zero of
the ZFC polynomial**.

## 5. Logical scope and attribution

The comparison snapshot is
`84e16e43092614bae262ca59651cb9d77e31a255` of
https://github.com/VladimirReshetnikov/ProveIt . The native source34 tuple
retains its earlier coefficient-binding commit, recorded in its original
binding file. Fixed payload bytes, rather than a new tuple name, determine
the constants.

The exact direct endpoint is C222(1) iff finite ZF refutability iff finite
ZFC refutability. The two inherited unconditional calibration theorems and
the source definition of ConZFC are printed and traced in
`inherited/direct/ENDPOINT_AND_PROOF_CHAIN.md`. The native dependency chain
is recorded separately in `inherited/native/README.md`.

The new equivalences have unbounded ordinary proofs. Their interpretation
as consistency statements uses the existing native/compiler or direct
C222/calculus theorem as an explicitly cited mathematical dependency.
The checkers prove the indicated finite algebraic claims; they do not
replace those unbounded proofs, re-verify the entire logical calibration,
prove Con(ZFC), or prove absence of integer roots. No new proof-assistant
endpoint is asserted.

The new work is offered for incorporation in ProveIt. Upstream proof and
code notices are retained; `LICENSE.UPSTREAM` is the repository's inherited
MIT No Attribution License. Exact sources and imported byte hashes are
recorded in the ledger and the subpackage provenance files.
