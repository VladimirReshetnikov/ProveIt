# Independent implementation audit

## Scope

Read-only review of the five programs in `output/ipra_equational_transport/code/`:

- `source_liberal.py`
- `equation_back.py`
- `compile_equational.py`
- `crossed_back.py`
- `compile_crossed.py`

No source edits were made during this audit. Verdict: no soundness or compilation bug found in the implemented proof-construction logic. This is source review and focused executable testing, not formal verification.

## Semantics checked

`source_liberal` faithfully generalizes the pinned calculus's Use term, Back source, and Close witness. The source of Back is checked to be a free scoped numerical variable. The target calculus checks the newest source and a literal-equation target. `opening` treats negative integers as free parameter levels and positive integers as locally bound coordinates; when replacing a negative parameter it returns the replacement immediately, so even a self-containing replacement is inserted once, not recursively resubstituted. Under positive openings its binder increments match the Eq/D/iterator syntax.

The `c` computation node accepts zero or a syntactic successor counter. The `valid` grammar plus the two-element unpack of a nonzero counter excludes arbitrary counters from the successor computation rule. Derived equations and clauses remain well scoped under the inherited invariant.

The Cross checker validates one supplied term. It destructures both premises as equations; the major source must be the newest parameter, and the minor's left endpoint must equal the opening of the supplied term. It returns the minor's unchanged right endpoint and the supplied term in crossed order. In particular the right endpoint is allowed to contain the source parameter and is not accidentally substituted.

## Compiler logic checked

The persistent constructors regenerate a derivation in the exact requested context/scope. They do not transplant a completed derivation to a later world. Assumption families use fixed context indices, preserved under append-only extension. `use_at` opens a fresh alias for arbitrary specialization, supplies the antecedent at the extended world, and discharges that alias before returning.

Atomic transport implements the forward convention `s=t, F(s) -> F(t)` consistently: it aliases the target t, derives the fresh parameter equal to s using symmetry, uses equation Back on the supplied source family, and exports F(t).

In the compound branch of `transport`, the source D-formula is opened at b, target Close selects that same b, and its branch appends z. The zero-row transport uses the reversed equality; the successor-row transport uses the original equality. The source clause is specialized at S z through its persistent realizer. Both recursive transport calls have one fewer D binder. `diagonal_zero_row` uses I0 for both endpoints and atomic equality; it does not recursively call compound transport.

All six source compiler cases have the correct scope extension and variable mapping. The Back template `opening(translated_goal, value, old)` respects one-shot substitution when the source replacement contains `old`. The Close case aliases the source witness, transports the actual assumption to a realizer of the source assumption, compiles a proper source subderivation, transports its result back, then closes and discharges. Source/target diagonal modes are preserved by the injective map on free parameter levels.

The crossed postprocessor replaces equation Back with exactly two Cross nodes. For a goal a=d and major b=t, the first produces d[t/b]=a and the second produces a=d. The same major proof is repeated at the same world, so neither renaming nor weakening is assumed.

## Focused executable checks

In addition to the parent's baseline fixtures, I ran 15 open-sequent compiler checks. Each used scope 2, a Back source at the older parameter -1, and the non-order-preserving injective map {-1:-3, -2:-1} into target scope 4. The five goal templates included an equation, nested D binders, a diagonal progressive matrix, and iterator terms referring to an enclosing D binder. Each was tested with three self-containing replacements:

- S(b), encoded `[0,-1]`;
- I(0,b;u.u), encoded `[0,-1,1]`;
- I(c,b;u.S(u)), encoded `[-2,-1,[0,1]]`.

All 15 source judgments were accepted, all equation-only translations derived the renamed target judgment, and all 15 two-Cross postprocessed translations derived the same judgment. These tests target scope mapping, replacement sharing, binder depth, and the unchanged-right-endpoint convention; they are not a completeness proof.

## Issue found and fixed

The first version of `compile_crossed.convert` recursively processed every non-None Use premise. The checkers intentionally ignore that slot for an antecedent-free clause, so an accepted source certificate containing arbitrary unused payload could fail conversion. The documented source-to-Cross pipeline was unaffected because the first compiler already emitted `None`, but the helper's advertised arbitrary-certificate domain was too broad.

The final implementation is context-aware. It carries the current context and scope through Alias, Open, and Close, examines the selected Use clause, and drops the unused premise when its antecedent is empty. I reviewed those context updates against `equation_back.derive`; they agree exactly. A focused regression passed for both a closed alias derivation with an ignored dictionary payload and an open antecedent-free Use with an ignored integer payload. Both were accepted by the equation checker, converted with `None` in the ignored slot, and accepted by the Cross checker.

The checkers should be described as performing rule-directed validation of all used terms, formulas, and premises. They do not claim to reject arbitrary data in a slot their semantics explicitly ignores. Ignored payload cannot affect the derived judgment.

## Audited source hashes

- `source_liberal.py`: `2844ec8efe49f398e8fe39cb0040d9d265297472837896da7e88b66016d23bb0`
- `equation_back.py`: `484de9ead68107090e33f3550b1b64f486262b557d3fba0dad1fa2004d6fceca`
- `compile_equational.py`: `2334cfea4b9852fc2507b14b09d945cb9abb06fe4b2fcb977b13e9d498092ca5`
- `crossed_back.py`: `ca462d240ed9a92d4a652c04728e9679abddf9e479c7a833ce9fbfe843f68f70`
- `compile_crossed.py`: `934c97d3aa193d4e68403ca03f26b70ab53579751bc3045c33e5804013e6c097`
