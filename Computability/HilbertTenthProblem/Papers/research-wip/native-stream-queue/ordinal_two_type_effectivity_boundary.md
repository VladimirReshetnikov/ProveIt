# A two-type promise boundary for effective ordinal semantics

This proof-only note records a stronger promise obstruction than the invalid-code decoder example already in the repository. Even among uniformly decidable strict well-orders on the fixed domain `N`, all promised to have type either `omega` or `omega+1`, there is no uniform terminating test for which of the two types occurs. Moreover, the `omega+1` side has no uniform existential finite-integer certificate with an effective verifier, even if that verifier is required correct only on the promised domain.

The construction was proposed by root and independently checked here. It limits isomorphism-invariant ordinal semantics on arbitrary program presentations. It does not refute the Beyond Ord manuscripts' explicitly restricted coefficient/constructor interfaces, and is not a new universal-compiler or operation-count claim.

## 1. A computable family entirely inside the promise

Fix a standard effective enumeration of machines run on their designated input. Write `H_e(n)` for the decidable predicate that machine `e` halts at some time at most `n`. Time zero is included; equivalently, an initially halted machine satisfies every `H_e(n)`. The predicate is monotone in `n`.

Define a strict relation `<_e` on `N={0,1,2,...}` by

```
x <_e y  iff
    x,y > 0 and x < y in the usual natural order; or
    x > 0, y = 0 and not H_e(x); or
    x = 0, y > 0 and H_e(y).
```

In particular, `0 <_e 0` is false. Each comparison uses only a bounded simulation, so the two-place characteristic function is total, uniformly computable in `e`. An index `p(e)` for that total comparison program is computably obtained by inserting `e` into this fixed algorithm. No unbounded halting decision is hidden in the map `e -> p(e)`.

The positive integers below `0` form an initial segment of the usual positive order, because `H_e` is monotone. All remaining positive integers lie above `0`. Thus the relation is a strict linear order: it is exactly the natural positive order with `0` inserted at that cut. This also proves transitivity, including triples containing `0`.

If the machine never halts, every positive integer lies below `0`, so the order is

```
1 <_e 2 <_e 3 <_e ... <_e 0,
```

of type `omega+1`. If it first halts at time `t`, put `k=max(1,t)`. Then the order is

```
1 <_e ... <_e (k-1) <_e 0 <_e k <_e (k+1) <_e ...,
```

where the first segment is empty for `k=1`. Its type is `omega`. This handles halting at time zero or one without an off-by-one exception. Both cases are well-orders, and every generated index lies in the promised two-type domain. Consequently

```
type(p(e)) = omega+1  iff  e never halts;
type(p(e)) = omega    iff  e halts.                 (1)
```

## 2. Canonical codes and ordinal comparison

Suppose a uniform effective procedure terminates on every program in the promised domain and produces a representation on which equality to the ordinal `omega` is decidable. Composing it with `p(e)` and that equality test decides halting by (1), a contradiction. It is enough that termination and correctness hold on promised inputs; behavior on all other programs is irrelevant.

In particular, a finite-string canonical-code map with decidable code equality cannot exist for all these program presentations. If a separate canonical code for `omega` is not supplied, run the assumed map once on the fixed presentation obtained from an immediately halting machine. Literal equality to that output then decides (1). This uses semantic canonicity; syntactically distinct codes that may denote the same ordinal do not give such a test automatically.

The same obstruction excludes a terminating isomorphism-invariant comparison of these presented order types against fixed `omega`: on this promise, `omega < type(p(e))` holds exactly on nonhalting machines. Comparison between individual elements *inside* each order is already decidable and is not at issue.

## 3. No effective finite witnesses for the upper type

Suppose there were a decidable relation `V(p,w)` on program indices and finite integer tuples, uniformly usable on the promised domain, such that

```
type(p) = omega+1  iff  there is a finite integer tuple w with V(p,w).
```

Enumerate all finite integer tuples and run this verifier on `p(e)`. This would enumerate exactly the nonhalting indices by (1). That is impossible: the halting indices are computably enumerable, and if their complement were also computably enumerable, dovetailing the two enumerations would decide halting. The usual diagonal machine, which halts exactly when its putative halting decider says that it does not halt, rules out that decider.

The argument also works for a computably enumerable verification relation by dovetailing the verifications. It therefore forbids a uniform ordinary-integer existential polynomial description of the `omega+1` property on these input indices, with computably supplied coefficients and parameters. Polynomial equalities and any finite decidable arithmetic side conditions can be checked on enumerated tuples. The obstruction already permits unbounded tuple lengths, provided finite tuples and their verification are effectively enumerated; fixed witness arity does not evade it. The same reasoning applies to positive-integer witnesses, signed-integer witnesses, or finite strings.

This is specifically an obstruction to the upper-type predicate, equivalently `omega < type(p(e))`. It is not a prohibition on all existential predicates about ordinal codes. For this generated family the other side has a finite certificate: a halting time `t` with `H_e(t)`. The proof also does not apply to transfinite witnesses, infinite tables, a non-effective verifier or an oracle for ordinal semantics.

## 4. Relation to existing repository evidence

The existing `review_definable_operations_de37a66d1.md`, Section B at lines48–50, constructs a computable order that has type `omega` when a machine does not halt and is ill-founded when it halts. The manuscript's total invalid-code decoder then yields a zero/nonzero distinction. That review explicitly leaves promised-valid representations and existential characterizations outside its conclusion. The present construction removes the invalid-code dependence: every input is already a well-order, and nonhalting is exactly the upper of two fixed ordinal types. It therefore excludes the particular upper-type existential certificate above. Neither statement is a blanket ban on Diophantine predicates or explicit ordinal constructor languages.

A bounded search of the native-stream-queue Markdown research notes for promise-valid, order-type/halting and canonical-ordinal phrases located that earlier decoder argument but no matching two-well-order proof. This is a repository-search observation, not a claim of mathematical novelty or an exhaustive literature audit.

The Beyond Ord source interfaces were reread at `beyond_ord/beyond_ord.tex:2037–2086` and `class_orders_beyond_ord/class_orders_beyond_ord.tex:1946–1992`. They explicitly distinguish arbitrary set ordinal coefficients, comparison relative to a supplied coefficient procedure, selected effective notation systems, and proof-carrying constructors. The latter source's actual finite artifact uses nonnegative integer coefficients. The obstruction above is consistent with these qualifications: finite program indices for arbitrary decidable coefficient orders do not themselves supply isomorphism-invariant ordinal comparison, even with the strong two-type well-order promise.

Explicit syntactic names for `omega` and `omega+1`, with structural comparison, are harmless. What fails is a uniform semantic conversion from every arbitrary program presentation in the constructed family into such distinguishable names. Merely promising well-foundedness, restricting the range to these two ordinals, or making each local order comparison terminate does not supply that conversion.

## 5. Immutable context and scope

The two repository review notes were read at commit `aa7a4193045635727d8b9f9da0e6bb2bd558dfb4`, under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`:

| Context | SHA256 |
|---|---|
| `review_definable_operations_de37a66d1.md` | `517cc3caf39e16e559802c3b8e50c5fee5efa2c754243be2cd8f18e9c8e67600` |
| Its immutable intake JSON | `59a506e0af06c463961d5bf3b089bcde6cf7c48f6da6cd5e8d32863884e93ea2` |
| `review_beyond_ord_e3839ad2c.md` | `04cd0623189d2273958c469e2fc6e1a93c4e92c3293c108043da9d8e4e1d43d6` |

The two underlying Beyond Ord TeX members are pinned at arrival `e3839ad2c6be32ac5c6fdc422507da07f85f4fb6`: `beyond_ord/beyond_ord.tex` has SHA256 `f5313160f48a17a24d7cc5ab8b9f0e6c9ba9acf3cdc5c87d41d9a8746ce8f3a4`; `class_orders_beyond_ord/class_orders_beyond_ord.tex` has SHA256 `89aefad6ae21160472a6d1a92885bf77c2237f4838247d0d8f5ec48b1ae342f4`. Their archive membership and read spans are recorded by the earlier intake; this note does not enlarge its proof certification.

This is a self-contained elementary computability argument, not a new source compiler, a Lean theorem, a class-order classification or a gate-count result. The bounded-simulation algorithms above are mathematical definitions; no supplied, archived, committed, frozen or copied program was executed or imported, and no repository file was changed. No source assertion was erased or newly labelled false. The stronger interpretation excluded here is expressly separated from the actual manuscript claims, consistent with the incoming retention rule.
