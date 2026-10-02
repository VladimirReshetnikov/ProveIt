# Three matrix equations for a canonical quantum inverse certificate

The [guarded compiler](quantum_three_equation_inverse.py) replaces the imported
report's four matrix equations by

\[
 \boxed{AG+P=I,\qquad AP=0,\qquad PG=0,\qquad A=I-T.}       \tag{1}
\]

The product order **PG** is essential. These three equations uniquely specify
the same group inverse `G=A#` and fixed-point projection `P` as the original
four-equation interface. The report's canonical rational-wire construction
then gives a unique natural witness for each fixed admissible rational `T`.
The corresponding parent and successor certificates have a bijection through
the common rational `(T,G,P)` interface and their deterministic intermediate
wires. They do not have the same witness coordinates or the same polynomial.

For matrix dimension `D`, the actual frozen generator emits

\[
 V=66D^3+9D^2+14\quad\text{natural variables},\qquad
 R=54D^3+6D^2+10\quad\text{quadratic residuals}.
\]

At `D=4`, the inverse core drops from **5,790 variables/4,730 residuals** to
**4,382 variables/3,562 residuals**, retaining uniqueness. The rational circuit
saves exactly `D³` multiplications and `D³` additions/subtractions. These are
rational-circuit counts. This packet does **not** claim an arithmetic gate
count for the final integer polynomial, compile a complete quantum moment
interface, or improve a universal Diophantine operation bound.

## 1. The imported source and exact construction

The source is the incoming archive
[Infinite Quantum Runs, Finite Diophantine Certificates](https://github.com/VladimirReshetnikov/ProveIt/blob/6914ccca6/docs/incoming/Infinite_Quantum_Runs_Diophantine_Certificates.zip),
committed at `6914ccca6`. Its complete SHA-256 is
`9da3025f7f93c5f2a2f8c33b7b467f70c0c0ec22587a07cc1983d0615de90ff4`.
The wrapper reads that exact working-tree archive, or retrieves the same
archive with a read-only `git show` at the pinned commit if its path is absent.
It rejects a different archive hash. It also pins the individual Python
members before loading their source into private modules:

|Member|SHA-256|
|---|---|
|`code/quartic.py`|`33991bd6d284ef935f2eee0b14db7a102beb613733dbf52ffd50232412e2c666`|
|`code/quantum_loops.py`|`1fa26c22f2ae6c16e5e701bcec58f83c6cd9c85f4611dc018f778be5d2fc9b63`|
|`code/verify_certificate.py`|`3a03bd538672918a79c1873507356e66b2f834405314e5347c58cd37669cc60f`|

The imported article's Sections 3 and 6 prove the original four-equation
inverse interface and canonical quartic compiler. This packet reuses the
**actual imported `Circuit` class**, including its seven-coordinate rational
wires, all sign and Bézout constraints, gate auxiliaries, pins and exporter.
It changes the dense inverse-core recipe: compute `AG`, `AP` and `PG`, then
compare `AG+P` to identity and the other two products to zero. It also runs the
actual original four-equation independent checker on every exported example;
all four decoded parent equations still hold.

The [receipt](quantum_three_equation_inverse.json) stores seven complete
sum-of-squares certificates, not merely cost predictions or sample matrix
answers. The original archive remains unchanged. Archive/member hashes,
canonical input data and scope metadata form part of each guarded packet.

## 2. Why the three equations suffice

This is a statement over rational or complex matrices. Suppose (1) holds.
Substitute `P=I−AG` into `AP=0` to obtain

\[
 A^2G=A.
\]

Therefore `rank(A)<=rank(A²)`. The reverse inequality always holds, so the
ranks agree. Equivalently, zero is a semisimple eigenvalue of `A` if present:
`ker(A)=ker(A²)`, and `ker(A)` intersects `im(A)` only in zero. Thus there is
a kernel/image splitting with

\[
 A=\begin{pmatrix}0&0\\0&B\end{pmatrix},\qquad B\text{ invertible}.
\]

Use this basis and write `G` in four blocks. From `P=I−AG` and `AP=0`,

\[
 G_{21}=0,\qquad G_{22}=B^{-1},\qquad
 P=\begin{pmatrix}I&0\\0&0\end{pmatrix}.
\]

Now `PG=0` forces `G11=G12=0`. Hence

\[
 G=\operatorname{diag}(0,B^{-1}),\qquad
 P=\operatorname{diag}(I,0),
\]

which are exactly the canonical group inverse and projection. The discarded
parent equation `GA+P=I` and its original condition `GP=0` follow. This proof
also covers an invertible `A` and `A=0`, using empty blocks. With rational
`A`, the splitting has a rational basis, so the unique pair is rational.

Conversely, the canonical pair satisfies (1). Thus the new and old rational
interfaces agree exactly. If zero has a nontrivial Jordan block, no new
solution can appear: `rank(A²)=rank(A)` already excludes it. Physical validity
of `T` is not needed for this algebraic result.

For a finite-dimensional completely positive trace-nonincreasing continuation
map, the imported report proves power boundedness and hence the required
semisimplicity. The new core can therefore replace the old core in that
setting. This wrapper does not itself certify complete positivity, trace
nonincrease, an exit instrument or an initial density.

## 3. Why reversing the last product matters

Simply deleting `GA+P=I` from the old four equations is unsound. Set

\[
 A=\begin{pmatrix}0&0\\0&1\end{pmatrix},\quad
 P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad
 G_t=\begin{pmatrix}0&t\\0&1\end{pmatrix}.
\]

For every rational `t`, `AG_t+P=I`, `AP=0` and `G_tP=0` hold. But `PG_t=0`
and `G_tA+P=I` require `t=0`. The receipt tests the concrete `t=1`
counterexample. Thus the saving depends on changing **GP to PG**, not just
removing a seemingly redundant equation.

## 4. Canonical natural witnesses and the exact ledger

Each rational wire retains the imported coordinates

\[
 (p,m,h,u,v_+,v_-,s)\in\mathbb N^7,\quad
 n=p-m,\ d=h+1,\ v=v_+-v_-,
\]

with `pm=0`, `v+v−=0`, `nu−dv=1`, and `u+s=h`. Here `N` includes zero.
These constraints uniquely specify a reduced signed fraction and its bounded
Bézout representative, including the fraction zero. Positive denominators
make all rational gate equations sound. Addition/subtraction uses five extra
natural coordinates and six residuals; multiplication uses three and four.
All intermediate rational gates are deterministic.

Equation (1) gives a unique rational `(G,P)` for fixed admissible `T`.
Canonical wires and deterministic gate auxiliaries therefore give exactly
one natural zero of the exported sum of squared residuals. The parent and
successor each have this unique lift of the same interface. This is a
bijection obtained by decoding `(T,G,P)` and rebuilding the appropriate
intermediate circuit; it is not a coordinate-deletion claim.

In the new dense schedule,

\[
 m=3D^3,\qquad a=3D^3-D^2,\qquad
 W=6D^3+2D^2+2,\qquad e=4D^2+2.
\]

Here `m,a` count rational arithmetic gates, `W` counts rational wire vertices,
and `e` counts pins/equalities. The schedule has three dense matrix products,
`D²` subtractions to compute `A`, and `D²` additions for `AG+P`.
Its input/unknown/constant wires are `T,G,P,0,1`. The imported formulas
`V=7W+5a+3m` and `R=4W+6a+4m+e` give the announced natural ledger.

|Matrix dimension|Parent rational M/A|New rational M/A|Parent V/R|New V/R|
|---:|---:|---:|---:|---:|
|1|4/3|3/2|111/89|89/70|
|2|32/28|24/20|754/614|578/466|
|4|256/240|192/176|5790/4730|4382/3562|

The exact savings are `22D³` natural variables and `18D³+D²` residuals.
The final polynomial is the sum of the squares of the complete listed
quadratic residuals and has exact formal degree four: each wire includes a
nonzero `pm` residual, and the highest parts of real squares cannot cancel.
This proves degree, not an optimized integer arithmetic circuit size.

Dropping wire canonicality would be a different, existence-only objective.
It is not done here: every canonical constraint from the imported class is
retained, and witness uniqueness is preserved.

## 5. APIs, defenses and verification

`build(t)` accepts a nonempty square list of lists of canonical rational
strings, such as `[["9/25"]]`. Integer strings, reduced fraction strings and
negative rationals are allowed; floats, Booleans, noncanonical fraction
strings and malformed shapes are rejected. Omitting `t` selects the scalar
geometric example. The construction accepts rational matrices with the
required algebraic index condition, including nonphysical examples; physical
interpretation remains a separate promise.

Each exported instance pins every entry of `T` to the supplied rational
constant using the imported `Circuit.matrix(..., pin=True)` interface.
This is a family of polynomials for fixed rational inputs, not one polynomial
with a free ordinary universal input parameter.

`checked`, `polynomial_source`, `evaluate`, `export_certificate` and `ledger`
require the complete exact-type canonical packet. `polynomial_source` returns
all sparse quadratic residuals; their squared sum is the polynomial.
`evaluate` accepts a separate complete natural assignment and returns that
integer sum of squares. `export_certificate` writes the complete certificate
in the imported checker's format. Public builds return defensive copies.
Input validation precedes caching, and a cold-cache mutation regression checks
that a returned packet cannot poison later canonical construction.

The seven emitted examples include zero and identity continuation, the
report's scalar geometric, partial-qubit and coherent-qubit inputs, a
nonsymmetric singular index-one matrix and an invertible Jordan example.
Each passes the imported independent checker's **four** decoded equations,
all actual quadratic residuals and a complete export/import round trip.
Every one of their 10,187 natural witness coordinates is separately increased
by one and rejected by an incident residual. The receipt also records 52
malformed-call rejections, the wrong-GP-order counterexample, and rejection
of index-two and index-three nilpotent obstructions.

Independent cross-review read the proof, wrapper and all three pinned source
members, and replayed the saved receipt. Additional checks covered nine
rational similarity cases in dimensions1–3, 72 full sparse-SOS comparisons,
nine leading-degree certificates, 78,125 canonical-wire assignments,
118 malformed calls and 18 nested cache-isolation cases. Root integration
review separately checked five emitted inputs and 35 malformed packets;
the report review compared 4,375 two-dimensional inverse assignments.
No unresolved finding remained in these reviews.

These exact finite checks supplement the general block proof and canonical
wire theorem. They do not prove physical validity or universal computation.
Run from the repository root with the existing SymPy environment:

```sh
/tmp/diophantine-research-venv/bin/python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/quantum_three_equation_inverse.py
```

Default mode recomputes and checks the saved receipt. `--write` regenerates
it. Temporary exported certificates are created only in temporary directories.
