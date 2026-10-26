# Arithmetic equation compiler: author checkpoint

2026-10-26. Author: root. The three new sources were fully read and freshly
compiled in order with `-M6000 -j1`, source-level async disabled, and the
private overlay `/tmp/arithmetic-expression-root-n6c1ese3` first in LEAN_PATH.
All final commands exited zero. Both main logs are empty; the checks log
contains exactly ten standard-only axiom reports and no warnings. Seven
generic reports use only `propext` and `Quot.sound`; three literal-current
bindings also inherit `Classical.choice` from existing definitions.

`ArithmeticExpression` compiles natural polynomial syntax into the ordinary
PAHF `0,S,+,*` language. Its binary numerals recurse on division by2 and
use `2*t` with a single recursive subterm. The compiler's evaluation identity
holds in every commutative semiring, with no induction or model-standardness
premise. Free-variable control proves that exactly n universal quantifiers
close the supplied n-variable equation. The no-zero sentence quantifies over
all tuples of the interpreted semiring; its natural-number specialization
is equivalent to absence of an integer-expression zero on natural inputs.

`ArithmeticCurrentEquation2011.unsolvabilitySentence` instantiates the exact
existing current expression, including all four complete coefficient ports,
after replacing each variable by its natural successor. Its standard
semantics is precisely absence of a positive integral zero of the maintained
polynomial. Its all-semiring semantics retains every tuple and exact signed
positive/negative expression parts. It does not define or assume an arithmetic
ZFC checker, nor prove HA/PA's desired equivalence. Satisfaction in the natural
numbers is explicitly distinct from an HA derivation.

Focused checks include literal binary constructors at0,1,2,3, arbitrary
semiring numeral evaluation, zero-variable equations at0 and−7, both signed
parts at a nontrivial coordinate slot, sentence closure and literal-current
domain binding. No enormous coefficient or split-expression tree was
expanded. There is no `sorry`, new axiom, native evaluation or increased
proof cap. Small numeral identities use kernel evaluation.

| Source | Lines | SHA-256 |
|---|---:|---|
| ArithmeticExpression | 144 | `19fe455df9e5a2f504af9cddcc4f3af10522c97f11f119e20b64195cf96b7baf` |
| ArithmeticCurrentEquation2011 | 50 | `54d3e6f824d4233dfcff4a7538f928729f39f237dbe422946b6218bf9b4d6d5b` |
| ArithmeticExpressionChecks | 60 | `abe90b2ae83176285419f673f065a32d78b4777fd4bc54198314af533f614374` |

The dependency/output/log pins are in `arithmetic-expression-replay.json`.
The final overlay uses the already reviewed object-current root and HA peer
overlays:133 custom primary objects and their available companions. All
referenced object hashes were rechecked. Their earlier source/cache evidence
retains its original scope; no fresh prerequisite closure is claimed here.
The main final object hashes are `230df320b30289bdbfe2e3aa949db11bccfb5e6d13232a2c7b7ecafe010023de`
and `57c250f9d92f92d55a2c7badfcd9cc1988890c73f362beeea1397c3f70b35aed`;
the checks hash is `73730bada463e29e8144443236601eca498651eb6706fe3726d0ba622752c5c0`.

The initial compiler attempt exposed numeral-cast/simplifier elaboration
issues; the current binding needed one explicit unfolding of its protected
alias; a first check needed the natural-evaluator bridge. Those failed logs
are retained and no failed object is accepted. An unrelated overlay-combining
attempt stopped on a conflicting prior NativeHalfBinomial object before
compilation; the final overlay excludes that unrelated overlay completely.
No shared object, existing source, equation artifact or Git state was changed
by the new compiler builds. Independent review remains separate.
