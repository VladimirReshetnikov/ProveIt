# Independent proof review: the fused exact mask

## Scope and certificate language

This review applies to the fixed keyword-only-mask checker and its uniform-update variant `novel/exact_uniform3.py`. It does not endorse the discarded four-positional-argument prototype. The whole-input alphabet guard first guarantees that all parsed nodes are actual integers or actual lists. In particular, Python `True` cannot bypass the integer test: its printed form contains forbidden characters.

The reference is `ipra_composition_and_dummy_slots_2026-11-13/code/checker_exact.py` at the pinned revision. Its canonical grammar uses zero code 1, variable codes 3+2j, successor `[t]`, iterator `[n,a,h]`, equality `[s,t]`, and paired binder `[B]`. A binder environment is a finite Boolean list `available`, nearest slot first. D prepends two genuine slots; successor prepends two dummy slots; iteration prepends a dummy slot in its counter and seed and a genuine slot in its state body.

## Finite forbidden-mask invariant

For n slots define

    F(available) = 2 * sum((1-available[j]) * 2**j for j in range(n)).

The low bit is zero: zero code 1 is never forbidden. At a formula position the depth is d=2n; at a term position it is d=2n+3. These depth identities follow directly from the unchanged update `d+5-len(a)`.

The updates are:

| Position | New slots | New mask |
|---|---|---|
| D body | true, true | 4F |
| Successor child | false, false | 4F+6 |
| Equality side | none | F |
| Iterator counter or seed | false | 2F+2 |
| Iterator body | true | 2F |

For an integer leaf the conjunction

    0 <= a < d and (d & a & (~F >> (a//2)) & 1)

holds exactly for a valid canonical term leaf. The final low-bit mask simultaneously tests that d is odd, a is odd, and a's slot is not forbidden. At a=1 it tests the always-allowed zero bit. At a=3+2j it tests availability[j]. The upper bound excludes slots beyond the current finite environment, which a finite forbidden mask by itself cannot exclude. Every formula-level scalar is rejected because d is even.

The arity gate permits precisely arity 1 at either sort, arity 2 at formula positions, and arity 3 at term positions. An invalid arity reaches the scalar branch and fails its integer comparison. Empty lists are rejected in the initial scan.

Consequently the initial opening, with g empty, returns the input unchanged precisely when the reference exact grammar accepts it. Otherwise it raises an exception. No proof-search property is used in this argument.

## One arithmetic transition

The uniform-update variant computes, for arity L and child index j,

    F' = (F << ((L+1) % 3)) + (d % 2) * (6//L - (j//2)*2).

The preceding arity gate leaves only these cases:

* L=1: shift by 2, j=0; the added part is 0 at D and 6 at successor.
* L=2: shift by 0; the parent is a formula so the added part vanishes.
* L=3: shift by 1; the parent is a term and the added part is 2 for j=0,1 and 0 for j=2.

This is exactly the table above. Caching L by `l:=len(a)` in the preceding positional argument is valid because positional argument values are evaluated before the following keyword argument. The assignment belongs to the current lambda invocation, so recursive calls cannot change a caller's l. The current implementation has 379 significant tokens, 433 AST nodes, and 690 normalized bytes under CPython 3.12.14.

## Transfer to the unchanged proof kernel

Python evaluates the left operand of membership completely before its right operand. The initial `i(goal)` therefore finishes before `g.append([])` makes g nonempty. Every later call observes a nonempty context. The mask-related tests and update calculations are then bypassed by `g or ...`; the extra mask value is never inspected, and the opening returns exactly the same values or failures as the reference kernel.

The mask is a keyword-only parameter. Thus `i(*a,t,2)` still accepts its positional arguments only when a has one entry, exactly as in the reference. This requirement is logically essential: allowing a fourth positional argument would let a binary equation pass the introduction's arity check.

The new reader drops only the reference's separate grammar traversal. On a canonical goal, the fused first scan is successful and unchanged, after which the same kernel operates on the same certificate data. On a noncanonical goal, both reject. On malformed top-level data, forbidden alphabets, missing packets, and other invalid inputs, any difference is only which exception occurs. Therefore the complete checkers have the same accepted certificate values, in the ordinary ideal finite-resource interpretation.

Every soundness, theorem completeness, interpretation, and formula round-trip theorem established for the reference exact checker transfers by this acceptance-language equivalence. The construction changes syntax validation; it adds or removes no arithmetic or logical axiom.

## Independent executable checks

`novel/audit_exact.py` extracts the actual opening lambda from the candidate source and compares it to the reference grammar on 30,955 integer/list cases: random trees of depth at most 5 plus targeted nested genuine and dummy binders. It also compares the complete candidate and reference CLI on 37 legacy fixtures in ordinary and optimized Python, for 74 runs. All comparisons agree. Most legacy fixture goals are not canonical under the stronger exact grammar and both programs reject them. These checks are supporting evidence for the universal proof above.

## Restricted-expression reader

I also reviewed `frontier/expression/reader_proof.md`. The character whitelist admits only decimal digits, minus, square brackets, commas, and the specified whitespace. Successful expression values are closed under integer/list construction, integer negation/subtraction, and list indexing by an integer. Top-level tuple results have no `.pop`; tuple indices are rejected by lists; without parentheses a tuple cannot be nested as an ordinary list element or used as a subscript target. Names, calls, attributes, strings, imports, and comprehensions cannot pass the whitelist. Thus the reader is a restricted data parser, not execution of user-supplied proof code. It has the same finite integer/list value image as the JSON input plus whole-alphabet validation, with an explicitly different raw input syntax.
