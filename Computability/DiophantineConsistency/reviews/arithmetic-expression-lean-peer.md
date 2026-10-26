# Arithmetic expression compiler: independent peer review

2026-10-26. **PASS; no correction requested.** Reviewer:
`/root/controller_certificate`. ROOT authored all three reviewed modules.
I authored reused Carrier65, literal-kernel and several arithmetic-window
prerequisites, and previously reviewed HAProofs. This review is independent
of the new arithmetic compiler and current-sentence binding, not of every
prerequisite in the imported native chain.

## Exact source scope

I read the complete 144-line `ArithmeticExpression`, 50-line
`ArithmeticCurrentEquation2011`, 60-line checks, author receipt and replay
metadata before execution. I also read the complete natural-expression split
and semiring evaluator, the complete current object-expression/domain module,
and the relevant actual PAHF definitions and proofs: `PreModel`, `Term`,
`Formula`, term evaluation/free variables, formula satisfaction/free variables,
`Sentence`, `closeN`, `Free_closeN`, and `closeN_valid` with its environment
convention. The 66936-line PASyntax file was hash-compared, not represented as
a complete manual read. I reread the literal Carrier65 coordinate/front
definition, current port aliases and mask/kernel definitions, and the full
maintained TeX source for the equation binding. No page rerender was needed
or performed.

| Source | SHA-256 |
| --- | --- |
| `ArithmeticExpression.lean` | `19fe455df9e5a2f504af9cddcc4f3af10522c97f11f119e20b64195cf96b7baf` |
| `ArithmeticCurrentEquation2011.lean` | `54d3e6f824d4233dfcff4a7538f928729f39f237dbe422946b6218bf9b4d6d5b` |
| `ArithmeticExpressionChecks.lean` | `abe90b2ae83176285419f673f065a32d78b4777fd4bc54198314af533f614374` |

Author receipt SHA-256:
`344509b96a07147c6eb3b313a14145cc8287d48296d51a49aef903d1e671b663`.
The complete replay JSON matches the requested pin
`432c3b1603952c93cab465c3a07ca939913d84f334331b770a28968261419878`.

## Mathematical and syntax review

`binaryNumeral` is a term in the actual arithmetic syntax, using only zero,
successor and multiplication. For positive n, division by two strictly
decreases the recursive argument. The selected branch contains exactly one
recursive subterm: `2*t` or its successor, rather than two copies of t. The
evaluation proof uses the even/odd division identity over natural numbers
and then casts that identity into the supplied commutative semiring. It does
not assume that the semiring is characteristic zero, nontrivial or standard.
The closure proof eliminates every possible free-variable occurrence.

The compiler `term` respects its arbitrary coordinate map. The variable case
of `free_term` has the correct orientation `k = coordinates i`; neither
injection nor surjection of the coordinate map is silently required. The
integer expression is first split into its exact two natural-coefficient
expressions. Consequently no truncated natural subtraction substitutes for
the signed polynomial. Over an arbitrary semiring the interpretation is
equality of these two expressions; the theorem does not incorrectly assert
ring subtraction or cancellation there.

`noZeroSentence` applies `closeN n` to precisely one implication from the
compiled equation to falsum. That body has no quantifiers, so this introduces
exactly n universal quantifiers. Its coordinate i is the body's de Bruijn
slot i. `Free_closeN` raises a hypothetical remaining free index to `n+k`,
where the finite coordinate bound excludes it. The all-environment semantics
of `closeN_valid` uses the same actual `scons` convention. Extending an
arbitrary `Fin n` tuple by zero outside its range proves that all tuples are
covered, including n=0; there is no restriction to tuples of standard numeral
values inside an arbitrary structure.

The current instantiation refers to the literal `naturalExpression`, whose
underlying `expressionAt` is already proved equal to the entire Carrier65
polynomial. I checked its fourteen coordinate order and all four port uses
against that definition and the maintained equation. The fixed tuple is
`[beta, K, lowPort, highPort+beta]`; the source high-mask shift is included
exactly once. The kernel remains the complete fixed decoded-tile kernel,
not a new constant parameter or an assumed residue. None of the four large
constants is replaced by an uninterpreted symbol or additional unknown.

The successor substitution has the required direction: natural variables v
represent positive integers `v+1`. In the reverse standard-domain map,
strict positivity makes `(v−1).toNat+1 = v` exact. The all-semiring statement
carefully retains the successor-shifted split-pair semantics; it does not
call those elements positive in an arbitrary semiring. The natural-number
specialization is exactly the negation of `PositiveZero` for
`CurrentPolynomialWindow2011.polynomial`, whose domain is all strictly
positive integral fourteen-tuples. No machine, native-calibration, consistency
or desired arithmetic-equivalence premise is supplied to these new theorems.

## Independent private replay

I created `/tmp/arithmetic-expression-peer-controller-20261026`, excluding all
three new target objects. All 133 primary prerequisite references and their
copies in the author's overlay were rehashed before use; every pin matched.
The copy pass considered available companions and found 133 files in that
selected set. The 135 distinct source records in the inherited object-current
and HA metadata were also rehashed and matched. These checks were repeated
after the fresh builds, together with all new source pins. Metadata and output
comparisons are saved privately as `inputs.json` and `outputs.json`.

Inherited dependency scopes remain unchanged. In particular, the earlier
object-current receipt expressly reuses accepted native objects whose import
graph predates the added `QuadraticFiber` and `TotalDegreeBound` source imports.
Matching the recorded source and object hashes does not turn that older native
chain into a fresh complete-current-source closure. The independent closure
refresh remains a separate task. The HA syntax prerequisites likewise retain
their authenticated cache-reuse scope; PASyntax was not freshly rebuilt here.

The inherited metadata pins are:

- object-current dependency JSON:
  `afdd946ecf76e6c31da7badf138fffc378080b82f0c2e66b8e33b5fd059edddd`;
- HA dependency JSON:
  `f8163c4c5325f30e1e9adfa04fbe3501ef67518072c46ed411b94531ea7ee4ba`;
- Lean 4.32.0 toolchain file:
  `2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e`;
- Lake manifest:
  `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`.

I freshly compiled the three targets in dependency order with the private
overlay first in `LEAN_PATH`, using `lake env ... lean -M6000 -j1 -o ...` and
their source-level `Elab.async false`. All three first attempts exited zero.
Both main logs are empty. The focused log contains exactly ten intended
reports: the seven generic theorems use only `propext` and `Quot.sound`; the
three literal-current theorems additionally use `Classical.choice`. There are
no warnings, failures, new axioms or unproved declarations in these results.

All three fresh objects are byte-identical to the author's:

| Object | SHA-256 |
| --- | --- |
| `ArithmeticExpression.olean` | `230df320b30289bdbfe2e3aa949db11bccfb5e6d13232a2c7b7ecafe010023de` |
| `ArithmeticCurrentEquation2011.olean` | `57c250f9d92f92d55a2c7badfcd9cc1988890c73f362beeea1397c3f70b35aed` |
| `ArithmeticExpressionChecks.olean` | `73730bada463e29e8144443236601eca498651eb6706fe3726d0ba622752c5c0` |

Logs are `generic.log`, `current.log` and `checks.log` in the private overlay.
The first two have the empty-file hash; the checks log hash is
`f45194808b4771ca1ab1ae9e4e713422dde8751c61a4240c44d5a5a022201d78`.
The focused checks preserve literal binary constructors at 0 through 3,
arbitrary-semiring evaluation, the zero-variable constants zero and −7,
signed evaluation at coordinate slot 5, sentence closure and the exact
current positive domain.

This accepts the arithmetic equation sentence and its stated semantic
identities. It does not define the arithmetized ZFC checker, derive an HA or
PA proof of the consistency equivalence, or infer such a proof from standard
truth. No reviewed source, shared object, equation artifact or Git state was
modified; this peer receipt is the only new repository file from the review.
