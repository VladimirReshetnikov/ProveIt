# A smaller direct proof of dominated rho8

This packet supplies an implemented proof simplification for the current ProveIt
development, compared with commit
53269bcab1efc0f82d3022645bd7cf0c22d84959. It is independent of any change to the
215-state transition table.

The new Lean module proves the exact existing statement
DomRho8.rho8_all for every natural-number code. It replaces the auxiliary
syntactic deduction theorem with two applications of a pointwise implication
lifting lemma. The unchanged KCodeDom adapter also compiles. A separate direct
Coq mirror of the same argument passes coqc and coqchk.

## What changes

| Measure | Current upstream | This packet |
|---|---:|---:|
| Lean DomRho8 source bytes | 30,114 | 26,709 |
| Lean source lines | 517 | 453 |
| Retained bootstrap schemas | 58 | 58 |
| Retained CD schemas | 59 | 52 |
| Auxiliary Proof relation / deduction development | present | removed |
| Final root needs distribution cd106 | yes | no |
| Coq source bytes | 22,673 (reflected certificate) | 24,352 (direct mirror) |
| Coq source lines | 1,169 | 440 |

The Lean reduction is 3,405 bytes (11.31%). These are current-source comparisons,
not comparisons with the much larger historical versions already simplified by
earlier work. The Coq mirror is 1,679 bytes larger than the existing compact
certificate. Its benefit is a shared direct proof structure and the absence of a
reflection interpreter and 735-instruction certificate. The two Coq approaches
should be compared by maintenance and audit cost, not solely by source bytes.

The seven omitted schemas are cd100 through cd106. Every retained bootstrap and
CD schema is transitively needed by the selected derivation graph. This is a
pruned existing graph, not a claim of a shortest possible logical proof.

## The mathematical argument

Write I(a,b) for the unchanged arithmetic code wim a b. The hypotheses are
exactly those in DomImp(T):

* T(0);
* T(I(a,b)) and T(a) imply T(b);
* T(rho8(a,b,c,u)) whenever u <= a.

Here rho8(a,b,c,u) is
I(I(I(c,u),a), I(I(a,c), I(b,c))).
All variables range over arbitrary natural numbers. There is no well-formed
formula restriction and no injectivity assumption on wim. In particular the
native numerical equality I(0,0)=0 remains respected.

Three already derived schemas supply the final argument:

1. K: a -> (b -> a);
2. J: (a -> b) -> (((a -> c) -> a) -> b);
3. B: (a -> b) -> ((b -> c) -> (a -> c)).

To lift a *proved* implication a -> b under an antecedent x, use the retained
schemas

    cd99: (a -> b) -> (a -> (x -> b))
    cd88: (a -> (x -> b)) -> ((x -> a) -> (x -> b)).

Two applications of modus ponens therefore prove

    T(I(a,b))  ==>  T(I(I(x,a),I(x,b))).

This is the theorem lift_right. Its proof is a term of two modus-ponens nodes.
The orientation matters: B alone has the known implication a -> b in its second
curried position and cannot directly justify this lifting by one application
of modus ponens.

For arbitrary a,b,c,u, put

    q = (c -> u) -> c
    f = (c -> u) -> a
    g = a -> c
    d = b -> c.

J and K give q -> d. B gives f -> (g -> q). Lift q -> d first under g and then
under f, obtaining

    (f -> (g -> q)) -> (f -> (g -> d)).

One final modus ponens yields f -> (g -> d), which is exactly the required
unrestricted rho8 row. The classical content already present in J remains; the
argument simply avoids a general deduction-theorem construction.

The complete final Lean proof is:

~~~lean
theorem lift_right {a b : Nat} (hab : T (wim a b)) (x : Nat) :
    T (wim (wim x a) (wim x b)) :=
  h.mp (cd88 h a x b) (h.mp (cd99 h a b x) hab)

theorem rho8_all (a b c u : Nat) : T (Code254.rho8 a b c u) := by
  let q := wim (wim c u) c
  let f := wim (wim c u) a
  let g := wim a c
  have hqd : T (wim q (wim b c)) :=
    h.mp (basisJ h c (wim b c) u) (basisK h c b)
  exact h.mp (lift_right h (lift_right h hqd g) f)
    (composition h (wim c u) a c)
~~~

## Fresh verification and its scope

Lean 4.32.0 freshly compiled the 13-source dependency closure through the exact
unchanged KCodeDom module. The final audit reports

    DomRho8.rho8_all: [propext, Quot.sound]
    DomRho8.composition: [propext, Quot.sound]
    DomRho8.lift_right: [propext, Quot.sound]
    KCodeDom.cdom_iff_c222: [propext, Quot.sound].

The replacement module emits no warnings. One unchanged upstream TarskiComplete
module emits its existing unused-variable warnings. The raw logs, source hashes,
object hashes, and compiler identity are in verification/.

Coq 8.18.0 freshly compiled the direct mirror with two unchanged arithmetic/code
dependencies from elliotglazer/k230-rocq commit
3142e4dd980f0be12f4abb636c4ae2528afc17eb, then independently checked the result
with coqchk. Print Assumptions rho8_all reports "Closed under the global context."
Those two dependency files already use From Coq imports and match their pinned
Git objects byte-for-byte. No compatibility source edits were made. The final standalone build stages the sources under disjoint logical paths;
its direct proof and dependency logs report no warnings.

These are fresh checks of the dominated-row logical interface. This packet does
not claim to have freshly rebuilt the complete binary-machine-to-ZFC endpoint
with the replacement, and the independent Coq check used 8.18.0 rather than the
repository's full Rocq 9.1.0 endpoint toolchain. Rebuilding the repository's normal
endpoint and assumption audit remains the integration gate.

The proof change itself neither decreases the machine's state count nor supplies
an internal ZFC or PA arithmetization. Its finite direct schema proof should make
such an arithmetization easier to review, but that is a further formalization
task.

## Contents and integration

* formal/ contains the checked replacement and its 12 unchanged Lean dependencies.
* patches/domrho8-pointwise-lifting.patch changes the exact Lean module and its
  existing generator in the ProveIt tree.
* generator/generate_domrho8_lean.py regenerates the replacement from the pinned
  certificate and CD230 template text.
* generator/generate_domrho8_rocq_direct.py mirrors the retained direct schema
  proof into ordinary Coq proof terms.
* rocq/DirectDomRho8.v is the independently checked Coq mirror.
* inputs/ contains the two exact generation inputs.
* baseline/ contains comparison sources.
* verification/ contains raw compiler logs, kernel checks, byte counts and
  generation receipts.
* source-pins.json records the inspected upstream file identities.

The Lean patch removes the previously exported helper distribution because no
longer needed by the endpoint. The exact existing DomImp, composition, sub, and
rho8_all interfaces remain, and lift_right is added. An indexed repository search
found distribution only in historical compiler logs, and the unchanged immediate
adapter compiles. If preserving every incidental helper name is desired, retain
the seven distribution schemas and the helper while keeping the new final proof;
that preserves the proof-structure simplification with a smaller source saving.
Do not call the aggressive graph slice an unconditional public-API-preserving edit.

The generator also fixes a line-ending portability issue: the current Git CD230
template is LF text, while the old generator's SHA256 pin accepts only its CRLF
form. The revised generator first replaces CRLF by LF and then pins exactly the
same template text. No other normalization is admitted. Both hashes are recorded
in verification/generation_receipt.json.

### Reproduce the Lean check

With Lean 4.32.0 installed:

~~~sh
python3 build.py --lean /path/to/lean
~~~

To regenerate the source:

~~~sh
python3 generator/generate_domrho8_lean.py \
  inputs/dominated_rho8_full_certificate.json regenerated.lean \
  --templates inputs/149-dom-theory-ev-CD230.v
cmp regenerated.lean formal/BusyBeaver/ZFC/DomRho8.lean
~~~

After applying the patch in ProveIt, run the repository's usual endpoint build
and assumption audit. The sources and generated proof should remain the objects
of verification; compiled objects in this working packet are disposable.

### Reproduce the direct Coq check

Regenerate the source with:

~~~sh
python3 generator/generate_domrho8_rocq_direct.py \
  formal/BusyBeaver/ZFC/DomRho8.lean rocq/DirectDomRho8.v
~~~

With a normal Coq installation:

~~~sh
python3 build_rocq.py --coqc coqc --coqchk coqchk
~~~

The builder copies all three bundled source files into an isolated build directory,
compiles every module afresh, and runs coqchk. It accepts an optional --coqlib
argument. For the unpacked Debian layout used in this run, pass --coq-root instead.
The verified command lines and the independent kernel-check log are recorded in
verification/coq_kernel_receipt.json.

The current checked SHA256 values are:

    Lean replacement:
    0368667979f56c6f47456ec91e3942d9b6bb5b7254741ef9a9deb6c40f3f8790

    Direct Coq mirror:
    5844ac4217c5901e8e56b017d867763d13a1e57f7c9fbb2438287a7540aa9d19

All inherited source retains its original authorship and provenance. This packet
adds a final derivation, its dependency pruning, the generator edits, and the
independent direct mirror; it does not claim authorship of the retained Source149,
CD230, arithmetic coding, or first-order logic development.
