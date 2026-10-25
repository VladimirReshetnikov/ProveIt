# A completely materialized finite ring/pairing theory

This directory contains an actual finite first-order theory, including every
term and connective, constructed from the supplied balanced Gram quartic.
It has **11 closed sentences in a fixed eight-function signature**. Its
arithmetic circuit has **2,736 gates**, and its full formula syntax contains
**107,353 nodes**. The deepest sentence has **28 edges of functional syntax**.
The complete `theory.json` is **697,036 bytes**.

The mathematical statement established by this construction is

\[
\mathsf{ZFC}\vdash
\operatorname{Con}(T_P)
\;\longleftrightarrow\;
\forall\mathbf x\in\mathbb Z^{240}\;P(\mathbf x)\ne0.
\]

This is a finite-theory source artifact. It is not a newly compiled
Diophantine equation or a numerical formula code in the target binary-relation
language. The final section describes the remaining compilation work.

## 1. Files and reproducibility

Everything needed to rebuild and verify this component is in this directory.
Only Python's standard library is required. No network, external package,
proof assistant, or surrounding repository is needed to run these commands:

```sh
python3 -B build.py --check
python3 -B check.py
python3 -B -O check.py
```

The first command regenerates the five materialized JSON files in a temporary
directory and compares their bytes. `check.py` is a separately implemented
checker. It does not import `build.py`.

| File | Content |
|---|---|
| `source_equation.json` | Exact source: 240 variables, 177 quadratic residuals, and 13 signed cross products |
| `source_expanded_polynomial.json` | Complete collected quartic with all 5,803 nonzero coefficients |
| `DAG.json` | Every arithmetic gate, its earlier dependencies, input table, constant map, residual outputs, and output gate |
| `theory.json` | Literal, closed formula ASTs for the eight ring axioms, two pairing axioms, and the single circuit sentence |
| `metrics.json` | Exact syntax, depth, gate, and byte counts, with source/artifact hashes |
| `build.py` | Deterministic standard-library builder |
| `check.py` | Independent exact polynomial and syntax checker |
| `verification_receipt.json` | Machine-readable output of the successful independent checker |

The frozen input files are copied byte for byte from the balanced Gram
construction. Their SHA-256 hashes are:

```text
source_equation.json
d293792cd1eee936256d74d6171294bd37bcbc4b577b8abc3347b97c7d5beace

source_expanded_polynomial.json
2d0d436fb8c59c4aaf3954b25398e27944a75ede6a94c448f72a6aa014940d18
```

The independent checker pins these source hashes. A different polynomial
therefore cannot silently replace the supplied one through changes to source
metadata.

## 2. The fully specified polynomial and arithmetic DAG

Write the source residuals, in their stored zero-based order, as
\(r_0,\ldots,r_{176}\). The polynomial computed by the DAG is exactly

\[
\begin{aligned}
P={}&\sum_{i=0}^{176}r_i^2
-r_{12}r_{16}-r_{12}r_{19}-r_{12}r_{17}
-r_{49}r_{51}-r_{19}r_{51}\\
&-r_6r_{21}-r_{17}r_{26}-r_{15}r_{21}
+r_{14}r_{21}+r_{17}r_{19}
-r_7r_{19}-r_7r_{17}+r_6r_{50}.
\end{aligned}
\]

The residuals contain 1,176 terms and 39 distinct signed coefficients, all of
absolute value at most 72. No coefficient is left as an unspecified recipe:
every integer constant is computed from literal `0` and `1` by binary doubling,
addition of `1`, and unary minus. For a positive integer \(c>1\), the builder
computes \(h=\lfloor c/2\rfloor\), then \(h+h\), and adds `1` if \(c\) is odd.
A negative integer is the unary negation of the positive construction. Gates
with the same operator and dependencies are shared in the DAG.

| Gate kind | Count |
|---|---:|
| Input | 240 |
| Literal `0` | 1 |
| Literal `1` | 1 |
| Unary minus | 254 |
| Addition | 1,200 |
| Multiplication | 1,040 |
| **Total** | **2,736** |

Gate IDs are zero-based list positions, and every dependency precedes its
consumer. The final output is gate **2,735**. Both the maximum gate depth and
output gate depth are **23 edges**, with input and literal gates at depth zero.
This circuit depth is a separate measurement from formula syntax depth.

The checker expands every gate as an exact sparse integer polynomial. It
compares the resulting output coefficient dictionary with the complete
source quartic, including all cancellations. It independently expands the
177 residual squares and 13 mixed products and compares that result as well.
It also checks the stored residual output gates, all declared constant values,
the binary constant chains, all variable indices, and gate acyclicity.
These are identities in \(\mathbb Z[X_0,\ldots,X_{239}]\); no evaluation at
sample points or search for roots establishes the binding.

The bound polynomial has degree **4**, support size **5,803**, and coefficient
height **6,404**. All 240 input coordinates occur in its collected support.
These are measurements of the supplied source polynomial, not a new endpoint
produced by the finite-theory construction.

## 3. The fixed language and ten background axioms

Equality is logical. The nonlogical signature has exactly eight function
symbols:

| Arity | Symbols |
|---|---|
| 0 | \(0,1\) |
| 1 | \(-,L,R\) |
| 2 | \(+,\cdot,\operatorname{pair}\) |

The following ten sentences are stored literally in `theory.json`. Their
universal closures are shown in full:

\[
\begin{array}{ll}
\forall x\forall y\forall w&((x+y)+w=x+(y+w)),\\
\forall x\forall y&(x+y=y+x),\\
\forall x&(x+0=x),\\
\forall x&(x+(-x)=0),\\
\forall x\forall y\forall w&((x\cdot y)\cdot w=x\cdot(y\cdot w)),\\
\forall x\forall y&(x\cdot y=y\cdot x),\\
\forall x&(x\cdot1=x),\\
\forall x\forall y\forall w&(x\cdot(y+w)=(x\cdot y)+(x\cdot w)),\\
\forall x\forall y&(L(\operatorname{pair}(x,y))=x),\\
\forall x\forall y&(R(\operatorname{pair}(x,y))=y).
\end{array}
\]

Let \(E\) denote these sentences. The first eight axiomatize commutative
unital rings, allowing the trivial ring. There is no separate nontriviality
axiom. The last two assert the projection identities. No relation such as
\(\operatorname{pair}(L(z),R(z))=z\) is needed in the theory.

## 4. Encoding every input and gate value with two variables

Pad the 240 input leaves to a balanced binary tree with **256 leaves**. For
\(0\le i<240\), let \(\pi_i(z)\) be the corresponding length-8 composition of
\(L\) and \(R\), reading the 8-bit index of \(i\) from most significant bit to
least significant bit, with `0` meaning \(L\) and `1` meaning \(R\). The first
step acts directly on \(z\). For example, with a two-level illustrative tree,
leaf `01` is \(R(L(z))\).

Likewise, pad the 2,736 stored gate values to a balanced tree with **4,096
leaves**. Let \(\rho_j(u)\) be its length-12 projection term. For each gate
\(j\), the actual syntax contains one equation \(G_j(z,u)\):

| Gate | Equation |
|---|---|
| Input coordinate \(i\) | \(\rho_j(u)=\pi_i(z)\) |
| Literal zero | \(\rho_j(u)=0\) |
| Literal one | \(\rho_j(u)=1\) |
| Unary minus of gate \(k\) | \(\rho_j(u)=-\rho_k(u)\) |
| Sum of gates \(k,l\) | \(\rho_j(u)=\rho_k(u)+\rho_l(u)\) |
| Product of gates \(k,l\) | \(\rho_j(u)=\rho_k(u)\cdot\rho_l(u)\) |

The eleventh sentence is

\[
\theta_P:=\forall z\;\exists u\;
\left(\bigwedge_{j=0}^{2735}G_j(z,u)\;\wedge\;
\neg(\rho_{2735}(u)=0)\right).
\]

In the materialized AST the complete list of **2,737 clauses**, in ascending
gate order followed by the output inequality, is joined using recursive
midpoint splits. This produces **2,736 binary conjunction nodes**, with leaf
depths 11 and 12. No schematic conjunction remains in the artifact. No
projection symbol \(\pi_i\) or \(\rho_j\), gate-name function, tuple function,
nonzero predicate, or additional numeral constant remains in the syntax.
Every occurrence is expanded to the eight fixed function symbols. Define
\(T_P=E\cup\{\theta_P\}\).

### AST grammar

Terms are the arrays

```text
["var", name]
["0"]                        ["1"]
["-", term]                  ["L", term]                  ["R", term]
["+", term, term]            ["*", term, term]            ["pair", term, term]
```

Formulas are the arrays

```text
["=", term, term]
["not", formula]
["and", formula, formula]
["forall", name, formula]
["exists", name, formula]
```

Variable and binder names are labels, not extra syntax-tree nodes. The JSON
document also gives the fixed signature and eleven sentence names as
metadata. Its `formula` fields are actual trees: sharing in the arithmetic
DAG does not create references or compressed subformulas in these trees.
The checker checks the grammar, symbol arities, variable binding, exact ten
axioms, each projection, each gate equation, conjunction shape, and final
inequality. All eleven sentences are closed.

## 5. Exact size and depth

Node counts count **tree occurrences**, including every repeated projection
term. Leaves, including variables and nullary functions, have depth zero.
An equality has one edge to each term argument; other constructors have one
edge to each immediate syntactic child. Quantifier names are labels.

| Measurement | \(\theta_P\) | Full 11-sentence theory |
|---|---:|---:|
| Formula nodes | 5,476 | 5,506 |
| Term nodes | 101,780 | 101,847 |
| **All syntax nodes** | **107,256** | **107,353** |
| **Maximum syntax depth, edges** | **28** | **28** |
| Formula-only depth, atomic formulas at depth 0 | 15 | 15 |
| Maximum term depth, edges | 13 | 13 |
| Quantifier nodes | 2 | 22 |
| Quantifier nesting depth | 2 | 3 |

The full theory is a list of sentences: there is no extra conjunction joining
the eleven top-level sentences. Its node counts are sums and its depths are
maxima. The two outer quantifiers of \(\theta_P\) are exactly \(\forall z\exists
u\), independently of the number of source coordinates and stored gates.

The 28-edge figure is the **functional syntax depth of this explicit AST**.
It is not the depth of a translation into a binary-relation language and is
not a logarithm of a numerical formula code. In general, the repeated
projection terms give syntax size \(O(m\log(m+n))\) and functional depth
\(O(\log(m+n))\), where \(m\) includes the resolved constant circuits.

| Materialized data | Bytes |
|---|---:|
| `DAG.json` | 226,080 |
| `theory.json` | 697,036 |
| `source_equation.json` | 129,271 |
| `source_expanded_polynomial.json` | 483,608 |

## 6. Proof of the consistency equivalence, formalizable in ZFC

The following proof uses only finite syntactic constructions, elementary
integer arithmetic, a concrete set model, and first-order soundness. The
checker verifies the finite polynomial and syntax data used by the proof;
it is not a proof-assistant formalization of ZFC or of this metatheorem.

### If the polynomial has an integer zero, the finite theory is inconsistent

Suppose \(P(a_0,\ldots,a_{239})=0\), with all \(a_i\) integers. Express each
\(a_i\) as a closed ring numeral, using unary minus for negative integers.
Put these 240 numerals into the first leaves of a balanced 256-leaf nested
`pair` term, and put `0` in its other leaves. Call the resulting closed term
\(z_{\mathbf a}\).

The two projection axioms prove that
\(\pi_i(z_{\mathbf a})=\overline{a_i}\) for every input coordinate. Instantiate
\(\theta_P\) with \(z_{\mathbf a}\) and use its existentially asserted gate
coordinates. By finite induction on the 2,736 gates, their equations and the
ring axioms prove that every \(\rho_j(u)\) equals the numeral for the integer
obtained by evaluating gate \(j\) at \(\mathbf a\). Literal constants and
input gates start this induction; addition, multiplication, and negation
preserve it.

The exact coefficient identity checked above makes the output value
\(P(\mathbf a)=0\). Thus the same finite premises derive
\(\rho_{2735}(u)=0\) and its negation. Existential elimination yields a finite
first-order contradiction from \(T_P\). The map from the given integer root
to this derivation is effective and formalizable in ZFC. Therefore ZFC proves
that \(\operatorname{Con}(T_P)\) implies the absence of an integer zero.

### If the polynomial has no integer zero, the finite theory has a set model

Assume \(P\) is nonzero at every tuple in \(\mathbb Z^{240}\). Use the ordinary
integer ring as the underlying set and ring interpretation. One explicit
choice of pairing transports Cantor pairing on \(\mathbb N\) through the
bijection

\[
b(k)=\begin{cases}2k&k\ge0,\\-2k-1&k<0,\end{cases}
\qquad
C(a,b)=\frac{(a+b)(a+b+1)}2+b.
\]

Interpret
\(\operatorname{pair}(x,y)=b^{-1}(C(b(x),b(y)))\), and interpret \(L,R\) as
its inverse coordinate functions. These are set functions available in ZFC
and satisfy the two projection axioms. They need not be terms in the ring
language: they interpret the additional primitive function symbols.

For any integer \(z\), the terms \(\pi_i(z)\) yield an integer input tuple.
Evaluate the finite arithmetic circuit on that tuple and encode its 2,736
gate values, padded with zeros, using the balanced 4,096-leaf pairing tree.
The resulting integer \(u\) satisfies every gate equation. Its output
coordinate is nonzero by the hypothesis. Hence this set structure satisfies
all of \(T_P\). First-order soundness, provable in ZFC for set structures,
gives \(\operatorname{Con}(T_P)\).

Combining the two implications proves the displayed equivalence. No claim
that either consistency statement is true is needed. If the accompanying
source calibration establishes

\[
\mathsf{ZFC}\vdash
\bigl(\forall\mathbf x\in\mathbb Z^{240}\;P(\mathbf x)\ne0\bigr)
\longleftrightarrow\operatorname{Con}(\mathsf{ZFC}),
\]

then composition gives
\(\mathsf{ZFC}\vdash\operatorname{Con}(T_P)\leftrightarrow
\operatorname{Con}(\mathsf{ZFC})\). This component binds its input polynomial
exactly and proves the finite-theory step. The input's original consistency
calibration remains a separate inherited dependency.

## 7. Uncompiled boundary

The existing numerical compiler's source language has a binary relation,
whereas this theory has function symbols. An improved literal Diophantine
endpoint would require an explicit translation into that exact target
language, its satisfiability/consistency calibration, the actual numerical
formula-code constant, and a replay of the arithmetic compilation with all
coefficients materialized.

In particular, replacing all terms by one long block of witness variables
can destroy the small-depth advantage. The overhead of a more careful local
or balanced relationalization has not been measured here. In pairing-based
formula codings, short formulas can still have very large expanded codes.
The counts in this directory cannot be substituted for a target formula code
or used to claim a new polynomial variable count or coefficient height.

The completed result is the explicit 11-sentence theory, its exact binding
to the supplied quartic, its measured functional syntax, and the ordinary
ZFC-formalizable proof above. Generic target-binary-relation translation and
coefficient materialization remain future work. No priority or optimality
claim is made.
