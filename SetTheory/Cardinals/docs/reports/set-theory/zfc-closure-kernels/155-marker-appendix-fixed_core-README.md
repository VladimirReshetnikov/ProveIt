# Optional appendix: a fixed-label nonlogical core

This appendix proves a separate equiconsistency theorem. It is **not a premise of the successful K217 construction**. It also records the exact cost of one direct source implementation: **211 distinct subtrees, 4,718 primitive occurrences**, before a binary implementation or initialization proof.

The point of the theorem is that the nonlogical seed core needs only one varying parameter. The general membership-vacuity row remains separate and retains both of its freshness inequalities. The proof is an ordinary modular adaptation of the included, pinned C222 Rocq source files. No new proof-assistant theorem or complete standalone Rocq build is claimed.

## Exact numerical definitions

For all natural codes, define

\[
P(x,y)=\frac{(x+y)(x+y+1)}2+y,\qquad
I(x,y)=4P(x,y),\quad R(x,y)=4P(x,y)+1,\quad
Q_x y=4P(x,y)+2,\quad E(x,y)=4P(x,y)+3.
\]

Write `x -> y` for `I(x,y)` and `N(x)` for `I(x,1)`. In particular, `I(0,0)=0` and `R(0,0)=1`. The code arguments range over **every natural number**; no well-formedness test or successful conventional formula decoding is assumed.

Use the exact seed terms

\[
\begin{aligned}
\operatorname{Req}(b,k,m)
 &=Q_b\bigl(m\to N(Q_b(m\to N(R(b,k))))\bigr),\\
\operatorname{Clos}(a,b,k,m)
 &=Q_b\bigl(R(b,k)\to N(Q_a(m\to
 N(Q_a(Q_k(R(k,a)\to R(k,b))\to\operatorname{Req}(b,k,m)))))\bigr),\\
J(a,b,c)&=Q_c\bigl(\operatorname{Clos}(a,b,c,c)\to N(\operatorname{Req}(b,c,c))\bigr),\\
V(a,b,c)&=R(a,b)\to Q_cR(a,b),\\
B(a,b,c)&=N\bigl(V(a,b,c)\to J(a,b,c)\bigr).
\end{aligned}
\]

Here J is `nks222` and B is `bundle222` in the included `Codes222.v`. The companion `KCode230.v`, `Codes230.v`, and `Thm222.v` supply the exact primitive definitions, retained rows, and proof rules. The apparently unusual uses of a formula code as a quantifier label are inherited unchanged.

## The fixed-core theorem

Let C be the inherited C222 numerical calculus. Construct Cfix by keeping truth 0, numerical modus ponens, theorem-only generalization, rho1 through rho6, G, and unrestricted rho8. Replace the old bundle clause by precisely these two clauses:

1. `V(a,b,c)` for all naturals a,b,c satisfying `c != a` and `c != b`.
2. `N(J(1,3,c))` for every natural `c >= 4`.

Then, formalizably in ZFC,

\[
(\mathrm{Cfix}\vdash1)
\quad\Longleftrightarrow\quad
\exists\text{ a finite ZFC refutation}.
\]

Equivalently, consistency of Cfix is equivalent to syntactic `Con(ZFC)`. Unrestricted rho8 may also be replaced by its independently calibrated restriction `U <= A`; the complete dominated-row certificate in the main package recovers unrestricted rho8.

### Upper refutation transfer

The included `Interp222.bundle222_proj` derives V(a,b,c) and N(J(a,b,c)) from the old B(a,b,c). Therefore both new clauses are old-C theorems. For the fixed core, `c>=4` guarantees both old inequalities with labels 1 and 3. Induction on a Cfix derivation translates it into a C derivation. The inherited endpoint `Sound222.thm222_sound` turns a C derivation of 1 into a finite ZFC refutation.

This is a syntactic refutation transfer; it does not assume semantic soundness or consistency of ZFC.

### Lower refutation transfer

The included files make the required modularity explicit:

- `CD222.v` derives the implicational basis from rho8 alone. `Prop222.v` and `G222.v` do not invoke the bundle clause. Their uses of retained axioms and proof rules can be read with the predicate Cfix.
- In `Interp222.v`, the only use of `W_bundle` derives the general fresh membership-vacuity row. Cfix now has that row directly. Thus `lprov_thm222` and the pure-logical/equality interpretation used downstream transfer to Cfix. `L224E.v` is included to expose that equality interpretation.
- In `Complete222.v`, the only additional bundle use is `Q_seed`. It asks for `B(1,3,seed_code(phi))`. The same module proves `seed_code(phi)>3` and its required freshness property. Definitions of the named seed used there are in the included `Sound222.v`.

For every `c>=4`, Cfix has V=V(1,3,c) and N(J), where J=J(1,3,c). It reconstructs the old bundle as follows. Temporarily assume `V -> J`; applying it to the theorem V gives J, and applying the theorem `J -> 1` gives 1. The K/S deduction transformation discharges that one assumption, giving `(V -> J) -> 1`, exactly B(1,3,c). No generalization occurs under the temporary assumption.

Consequently the required `Q_seed` instance is available. The remainder of `Complete222`, including the interpretation of the K0 axioms and the inherited ZFC-to-K0 refutation transfer, is unchanged. This gives the lower direction.

The theorem claims **equiconsistency**, not equality of every theorem code of C and Cfix. It does not license deleting either inequality on the separate V row.

## Exact direct source evidence

The baseline is the frozen dominated source with hash

```text
264fba90229974a53c2c5c943cf5fe8924327b6bbc31bd47e64d7f5c670b7495
```

The direct construction replaces the old bundle-emission forest at zero-based primitive interval `[2657,4570)` by two consecutively emitted formulas:

```text
N(nks222(1,3,c+4)); V(a,b,c)
```

The first formula is constructed before V and goes onto the formula stack when V is constructed. The original two equality gates then guard V, exactly as required. The fixed core uses `c+4`, ensuring its bound for every raw natural selector c. Adding four occurs only in the formula top register; the original selector remains unchanged for the V gate.

The inherited closed macros have these contracts, with the two scratch registers zero at entry and exit:

- `push` sends old top t to the paired stack `P(t,w)` and sets top to zero.
- A parameter load is `push` followed by a copy of register 4, 5, or 3 to top; the parameter is preserved.
- I, R, and Q replace two formula-stack operands by their exact numerical constructor and preserve the remaining stack and nonformula data.
- An increment of register 1 increments only the formula top.

Thus the constant 1 load is `(push,inc1)`, constant 3 is `((push,inc1),(inc1,inc1))`, and the c+4 load is `(load_c,((inc1,inc1),(inc1,inc1)))`. The verifier matches each inherited macro against exact primitive intervals of the baseline, reconstructs the source bytes, and independently parses the replaced primitive word into the two displayed symbolic formulas. All macro factors are closed. This is an all-natural formula-emission identity under the inherited macro contracts.

| Source | DAG nodes | Primitive occurrences | Maximum depth | Maximum zero run | Logical status |
| --- | ---: | ---: | ---: | ---: | --- |
| Baseline dominated source | 203 | 4,751 | 45 | 6 | Main package calibration |
| Direct fixed labels 1,3, using c+4 | **211** | 4,718 | 46 | 9 | Fixed-core theorem above applies |
| Direct labels 0,1, using c+2 | 210 | 4,673 | 46 | 9 | Separate lower-proof adaptation not supplied |
| Reassociated labels 0,1 variant | 210 | 4,673 | 47 | 6 | Same missing adaptation; unused |

The direct fixed1,3 source is `source/fixed13_direct211.json`, hash

```text
28bed81217da333bf794619d12ea2b5462ee1f00a46acb82d8e179980279d5ef
```

The 210-node alternatives change the frozen logical roles from 1,3 to 0,1. Their formula words and source control graph are checked, but the precise `Complete222` lower proof uses named environments specialized to 1,3. A variable-renaming adaptation is required before asserting their own lower calibration. They are included only to document the earlier source measurement; neither is a premise of K217 or of the fixed1,3 theorem. Their rebracketing was found earlier; this appendix performs no discovery search.

The source replacement adds one formula to AX's output stack. No complete revised command-block compiler, binary table, initialized runtime, or physical state count is claimed for these optional sources. In particular, 211 is a count of distinct source subtrees, not 211 Turing-machine states. The direct source's maximum zero run of 9 would also need addressing before using the present engine. It does not improve the delivered K217 candidate.

## Replay and provenance

Run with Python 3 and assertions enabled:

```sh
python verify_fixed_core.py --output source_receipt.json
```

Or pass this appendix directory as the first argument. The verifier uses only the standard library, rejects optimized Python explicitly, authenticates every copied input against `provenance.json`, reproduces both direct sources byte for byte, checks the symbolic emitted formulas, checks exact guarded control graphs and all 186 protected non-AX paths, and measures the frozen reassociated alternative. No optimizer, network, proof assistant, or external compiler is required.

The `theory_inputs` files are exact byte copies from ProveIt commit

```text
704b87442afbd571833a628cd558f1d207fd8b2f
```

Every file has its original repository path and SHA-256 in `provenance.json`. The included arithmetic and logical definition modules were already vendored in that repository from Elliot Glazer's k230-rocq work; their own attribution headers are preserved. `licenses/LICENSE-ProveIt.txt` is the repository's exact license. These are reviewed proof excerpts and definitions, not a complete buildable dependency closure of the original Rocq project. Inherited contributions and the broader proof chain retain the notices in the main K217 package.

`fixed_core.tex` is the corresponding standalone mathematical note. The appendix is independent of the main 217-state theorem.
