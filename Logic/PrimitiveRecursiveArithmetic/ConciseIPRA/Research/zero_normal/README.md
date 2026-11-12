# One computation axiom for iPRA

**Six primitive rules, one computation schema, and a smaller strict tagged checker.**

Prepared for Vladimir Reshetnikov, November 11, 2026.

Read [the paper](paper/report.pdf) or its [LaTeX source](paper/report.tex).

## Result

Use terms with no literal-zero-counter iterator. Capture-avoiding substitution
rebuilds terms with I(0,a;u.h) replaced by a. The zero computation proof rule can
then be deleted. Combine this with the existing single-introduction rule and
crossed one-context equality to obtain six primitive rules:

1. Hypothesis.
2. Successor computation.
3. Crossed one-context equality.
4. Q elimination.
5. D elimination.
6. Witness-selected D introduction.

The new nonliteral representative of zero is I(1,0;u.0). It is canonical, and
successor computation proves it equal to zero. It replaces the erased alias
I(0,0;u.0) in the single-introduction argument.

The report proves bi-interpretability and equiconsistency with full first-order
intuitionistic primitive recursive arithmetic. Both domains are whole and
equality is actual; both numerical composites have identity graph x=y.
Only term syntax is normalized.

## Exact size comparison

Measurements use CPython 3.12.14, ast.unparse plus a trailing newline,
significant tokens, all AST nodes, and deterministic gzip level 9.
All validation and hereditary substitution are charged. The raw and canonical
term grammars intentionally differ.

| Checker | Rules | Tokens | AST nodes | Normalized bytes | Gzip-9 |
|---|---:|---:|---:|---:|---:|
| code/control_eight.py | 8 | 1084 | 1141 | 3322 | 984 |
| code/zero_seven.py | 7 | 1073 | 1136 | 3272 | 996 |
| code/control_seven.py | 7 | 1024 | 1080 | 3145 | 964 |
| **code/zero_six.py** | **6** | **1013** | **1075** | **3095** | **977** |

The conservative six-rule comparison saves **50 bytes, 11 tokens, and five
AST nodes**. Gzip increases and is informational.

This does **not** beat the separate 521-byte arity-coded frontier or prove a
global optimum. Earlier prevalidated_elimination and uniform_zero packages
already proposed definitional zero computation. It works here at lower cost
because the tagged initializer is outside the state binder, so erasure needs
no coordinate lowering.

## Run the checker

From this package's root:

~~~bash
python3 code/zero_six.py < code/examples/used_hypothesis_induction_one_zero_six.json
~~~

Acceptance is normal exit and exactly ACCEPT followed by a newline.
Rejection has a nonzero exit code. Full input syntax is in code/README.txt.
The checker uses only Python's standard library and imports no translator.

## Reproduce executable evidence

~~~bash
python3 code/verify.py
~~~

The recorded run includes:

- 500 process checks, ordinary Python and -O;
- 400 expected acceptances, 100 expected rejections, zero mismatches;
- all 64 inherited positive certificates translated into both normal kernels;
- 4832 substitution-commutation checks;
- 462 checks each of idempotence, scope preservation, and shift commutation;
- 400 checks each of zero erasure, successor computation, and formula roots.

The untrusted compiler code/translate.py handles the missing atomic case at
witness zero by transport through I(1,0;u.0)=0 and capture-avoiding replacement
of the local assumption. No checker imports it.

## Lean verification

The new 255-line formal/ZeroNormalization.lean compiled with Lean 4.32.0,
compiler commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, and Mathlib revision
81a5d257c8e410db227a6665ed08f64fea08e997.

It proves canonicality, idempotence, renaming/lifting, term and formula
substitution coherence, hereditary substitution composition, internal equality
t=nf(t), and both native formula normalization round trips.
Iterator-body normalization explicitly uses the inherited equation-induction
lemma Q.iter_congr.

See evidence/ZeroNormalizationAxioms.log. There is no sorryAx or added axiom.
Ordinary normalization correctness uses propext and Quot.sound; the native
return bridge additionally inherits Classical.choice.

**Boundary:** the full new six-rule derivability relation and equivalence,
and the Python checker, are not formalized in Lean. Those parts have the
written proof and executable translation tests.

To rebuild, put Lean 4.32.0 on PATH, obtain the pinned Mathlib checkout, and run:

~~~bash
cd /path/to/mathlib4
lake exe cache get Mathlib/Data/Fin/Tuple/Basic.lean Mathlib/Tactic/Abel.lean
cd /path/to/ipra_zero_normal_2026-11-11
python3 formal/check_lean.py /path/to/mathlib4
~~~

The helper compiles frozen references and the new module under build/lean.
It corrects one inherited namespace reference in a working copy of
OneContextOneIntro.lean: WPrf.eqSymm becomes WKernel.eqSymm.
Frozen references stay unchanged; evidence/one_context_compatibility.patch
records the correction.

## Rebuild the paper

With a standard TeX Live installation:

~~~bash
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
~~~

The two table fragments come from the recorded evidence. The PDF is visually
checked. Only standard LaTeX packages are used.

## Provenance

Baseline: VladimirReshetnikov/ProveIt, commit
ecb3b847290c33b1ef7f04571cac63e97c73a54e, directory
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.

reference/ConciseIPRA contains frozen dependencies; reference/prior contains
the explicit earlier proposals; reference/foundations contains inherited
written arithmetic proofs. Upstream files retain the MIT-0 license.
evidence/provenance.json identifies copied sources; evidence/SHA256SUMS
covers the delivered files except itself.

The result is a local simplification of the direct presentation, not a global
minimum, a new foundational idea, or a replacement for the separate
521-byte programs.
