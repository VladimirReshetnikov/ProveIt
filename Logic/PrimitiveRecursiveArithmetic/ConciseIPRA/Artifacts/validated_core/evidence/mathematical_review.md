# Independent review of the final unified validator

## Reviewed files and conclusion

This note supersedes the earlier review of the intermediate 1,005-byte staged checker. The final reviewed files are:

- `code/native_typed_full.py`: 897 normalized bytes.
- `code/native_typed_eqd.py`: 878 normalized bytes.
- The immutable-tuple continuation used by `code/guarded_tokens.py`.

The final full checker preserves the existing fully typed Eq/Q/D certificate interface and the native consequence relation. Its simplification is to recognize the unrestricted integer/list certificate syntax and the scoped goal syntax with one recursive validator. The Eq/D interface is a separately labeled restriction on public formula syntax; Q resources remain available internally.

This is an independent written argument about the actual final source, not a new Lean verification of Python. The mathematical equivalence with iPRA is inherited from ConciseIPRA at commit `a4e5e96c456303cf231eab2aeeb3291d8889833f`.

The matched full control is `reference/native_typed_full.py`, copied from incoming reversal_core's `controls/control_shared_typed.py`. That control already uses `g=[0]`, the function sentinel `c`, and source-selected elimination. These features must not be claimed as new.

## Precise acceptance convention

Define V(a,d) to mean that the new call `v(a,d)` returns a truthy value normally. An exception means rejection. This distinction is necessary: for example, the full `v([],2)` reaches `a[0]` and raises, whereas the old goal validator returned false. Likewise `v(None,0)` raises on multiplication, whereas the old exact-type recognizer returned false. Neither difference changes acceptance.

Let J(a) mean that a is a finite tree containing only exact Python integers and lists. Thus externally supplied Boolean, floating-point, string, dictionary and null nodes are excluded. Let P(a,delta) be the previous scoped goal predicate, with delta=0 at a formula root and delta=3 at a numerical root. All equivalences below concern finite JSON values and successful acceptance, apart from ordinary host resource exhaustion.

## Universal validator equivalence

### Generic mode

For every finite JSON value a,

    V(a,0) if and only if J(a).

Proof is by structural induction on the JSON value. At an exact integer, the branch `not d` is true. At a list, `a*0 == []` is true, the local shape condition is true because d=0, and each recursive call receives `d and d+5-len(a)`, which is again zero. Hence the list passes precisely when each child satisfies J.

Every other JSON type either makes `a*0 == []` false or raises before returning truthy. For instance Boolean multiplication produces numeric zero, not the empty list; strings produce the empty string; dictionaries and null raise. This proves the equivalence, not merely one implication.

### Goal mode

For every delta reachable through an allowed goal constructor,

    V(a,delta+2) if and only if J(a) and P(a,delta).

The shift by two preserves parity. For an exact integer, the new test is

    (delta+2) % 2 and
    (not a or (2 < a < delta and a % 2)).

For integers, `not a` is equivalent to a=0 and `2<a` to 3<=a. This is exactly the old test: a scalar occurs only in a numerical position and is zero or an odd protected coordinate below delta.

At a numerical list node, delta is odd, so `len(a) in (1,2+d%2)` permits exactly arities 1 and 3: successor and iterator. In the full validator, the extra triplication disjunct cannot add another arity, because `a == [a[0]]*3` forces arity 3.

At a formula list node, delta is even. The full validator permits arities 1 and 2 directly, denoting D and equality. Its extra disjunct admits exactly the canonical Q arrays with three identical children. This is equivalent to the old test permitting arities 1,2,3 and requiring identical children in the arity-3 case. The Eq/D variant simply lacks that extra disjunct and permits formula arities 1 and 2.

For each permitted arity r, the new child depth is

    (delta+2)+5-r = (delta+5-r)+2,

so the induction hypothesis applies to every child. Starting from delta=0, allowed arities 1,2,3 increase delta by 4,3,2 respectively. Thus goal mode never accidentally enters generic mode d=0. All other shapes reject before any successful recursive traversal can create such a transition.

This establishes the full equivalence by structural induction. It is an unbounded argument for every finite JSON tree, not a finite-test claim.

### Prefix and goal jointly cover the original input

The final program first pops the last array element as the goal a and leaves the preceding certificate packets in q. It accepts the front end precisely when

    V(q,0) and V(a,2).

For a nonempty top-level JSON array, the two preceding equivalences identify this with

    J(q) and J(a) and P(a,0),

which is exactly the old global integer/list check followed by the old goal check. The extracted goal and the remaining prefix partition the original array, so no subtree escapes validation. Every non-array top-level JSON value, and an empty top-level array, rejects before entering the checker. The old interface also rejected these inputs.

The program then takes `q.pop` as its instruction source. No checker action occurs before both validation calls have succeeded.

## Opener invariant and unchanged proof semantics

After the front end succeeds, every input subtree is an exact integer or list. The checker creates only further list/integer data, harmless Boolean zero images, and a missing-image function sentinel that cannot be used successfully as numerical data.

For an integer, `a*0` is numeric zero. For a list, it is the empty list. Thus the new opener test `a*0 != 0` agrees with the old `a*0 == []` on every successful data case. A used function sentinel raises in both versions. No new inference is authorized by this replacement.

The inference engine otherwise retains the matched native calculus and its choice bit for case versus equational-progress introduction. The full strict checker is not the separate guarded deterministic-introduction calculus. In particular, the final full result needs no new guarded/public auxiliary-language bridge.

The inherited arity encoding has dummy numerical slots. Its soundness and completeness statements use the specified sorted decoding and intended encodings. No additional claim that every noncanonical raw alias is interchangeable is needed here: the new front end and the matched control have the same acceptance predicate.

## Immutable continuation loop

The separate compact token profile replaces the final recursive continuation by a loop. The retained context is a tuple. An extension `g += (h,)` rebinds a local variable to a new tuple, so recursively checking a major premise cannot mutate its caller's context. An in-place list extension would not be justified by this argument and could leak local hypotheses.

The loop maintains the same goal, context, instruction-stream position and global fresh-parameter floor as the recursive continuation. Major-premise recursion remains recursive. The fresh floor decreases at the same allocation points and is not restored on return. Reordering the two pure opening computations for the next goal and hypothesis preserves successful results; failure of either prevents acceptance.

This is a control-flow simplification, not a change to freshness, numerical substitution or the theory's induction strength.

## Neutral truth is inherited

The scalar formula representation 0 denotes the closed theorem 0=0. Adding a fixed closed theorem T to every retained context preserves consequence when weakening and assumption cut are admissible:

    Gamma,T |- A if and only if Gamma |- A.

For the restricted-source calculus, 0=0 is already derivable. Put c=I(0,0;u.0). Its computation equation c=0, used as both transport premises with F(v):=(v=0), yields 0=0; c is not the literal zero term. Cut requires no substitution of numerical terms into restricted sources.

This justifies the representation but supplies no new mathematical novelty: scalar truth already occurs in the matched incoming full control.

## Bi-interpretation transfer

The pinned `NativeBiInterpretation.lean` was fetched and inspected. It states `native_iff_pra`, `pra_iff_native`, `native_roundTrip`, `pra_native_roundTrip`, and `native_inconsistent_iff`. The pinned `NativeInherited.lean` states `iprf_iff_nprf`; `NativeZeroSource.lean` states `zprf_iff_nprf`.

The final full program preserves the matched native certificate consequence relation by the universal front-end equivalence and unchanged inference engine. Consequently the existing interpretations transfer unchanged. Both numerical domains remain whole, equality remains actual equality, and the numerical interpretation composites retain the identity graph. The construction introduces neither a quotient nor a standard-model restriction, and neither a new evaluator nor stronger induction.

For the separately reported Eq/D public interface, Q can be expanded definitionally as a D binder with an unused witness: Q_y B(y) is interderivable with D_{x,y} B(y), with x fresh and unused. This is inherited from the native bridge, not a new result of validator compression.

The Lean files were inspected but not rebuilt for this review. No new Lean theorem binding the final Python bytes to `NPrf` is claimed.

## Final metrics

The final figures are taken from the frozen `evidence/metrics.json`. They use CPython 3.12.14, `ast.unparse(ast.parse(source))` plus one LF, the entire module without docstring removal, and gzip level 9 with mtime=0.

| Complete program | Significant tokens | AST nodes | Normalized UTF-8 bytes | Gzip-9 bytes |
| --- | ---: | ---: | ---: | ---: |
| Matched full typed control | 450 | 514 | 1049 | 540 |
| Final unified full Eq/Q/D checker | 401 | 468 | 897 | 505 |
| Matched Eq/D typed control | 424 | 484 | 1000 | 522 |
| Final unified Eq/D checker | 390 | 454 | 878 | 498 |

The complete full interface saves 152 bytes, 49 significant tokens and 46 AST nodes against its matched control. The complete Eq/D interface saves 122 bytes against its matched narrower-syntax control. The earlier 1005/956-byte staged results are intermediate and are not the final deliverables.

Reviewed SHA-256 values:

- Full: `844fe59fcc7235d72daf5e351840ba315938689a3be4b1751ec6ef3375c17e8b`.
- Eq/D: `45d60248d39aafad877a55f151cadbad35f5861165f3495dde932176d9beae38`.

These are measured simplifications of complete checkers, not a proof of absolute minimality or a new axiomatization theorem. Separate compact-kernel profiles have different input contracts and must not be compared as if their omitted front-end checks were included.
