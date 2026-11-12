# Exact preservation of the typed native checker

The new `code/checker.py` composes two existing ideas: the whole-certificate
lexical integer/list gate of `validated_presentation`, and the scope reuse of
`scope_kernel`. It then stores only the formula/term distinction needed by the
remaining public grammar checker. It does not change the native scalar
axiomatization. The proof function `c` is unchanged from `reference/typed870.py`.

## 1. The input-type gate is unchanged

After `json.load`, the complete input's Python representation is checked with

```python
repr(q).strip('0123456789[], -')
```

An empty remainder means every JSON value is an integer or a list of such
values. Boolean representations, floating-point punctuation or letters,
string quotes, dictionary braces, and `None` all leave forbidden characters.
The whole certificate is checked, including unused prefix items. Both old and
new programs perform exactly this same test before reading the goal.

## 2. Separation of grammar and scope

The original validator's integer condition is

    d % 2 and (a == 0 or (2 < a < d and a % 2)).

Here even depths are formula positions and odd depths are numerical positions.
At every node with `r` children, the depth changes by `5-r`. Starting at root
depth zero, the grammar permits:

| Position | Node | Arity | Child position |
|---|---|---:|---|
| Formula | D | 1 | Formula |
| Formula | Equality | 2 | Term |
| Formula | Diagonal Q triple | 3 | Formula |
| Term | Successor | 1 | Term |
| Term | Iterator | 3 | Term |

Every permitted numerical position has positive odd depth at least three.
Drop only the bound `a < d`, retaining that a numerical leaf is zero or an odd
integer greater than two. The resulting validator admits some out-of-scope
leaves; no other grammar restriction changes.

The unchanged kernel begins each call by computing the entire expression
`i(a)` before checking membership in its context or reading a proof packet.
At the first call its floor is zero and its substitution image is the function
`c`, which is deliberately not a numerical tree. On a numerical leaf the
opening `i` behaves as follows:

* If `0 <= a < d`, it returns the same leaf.
* Otherwise the odd numerical depth forces an attempt to open the missing
  image `c`. Multiplying that function by zero fails, so the program rejects
  before it reads any proof instruction.

The relaxed grammar permits only zero or positive odd integers greater than
two. Thus an accepted initial opening supplies precisely its one omitted
condition, `a < d`. No invalid formula-position integer can bypass this
argument, because the grammar validator still rejects every such integer.

Consequently the original public grammar test succeeds exactly when the new
test and the already-existing initial scope opening both succeed. On those
goals, the opening is the identity. If the original test fails but the new
test succeeds, the new program rejects before consuming a certificate item.

## 3. A Boolean suffices for the remaining grammar

Once numerical upper bounds are supplied by the kernel, the validator needs
only whether it is visiting a term. Its next mode is

    numeric or len(a) == 2.

The table above proves this formula for every permitted constructor. A
formula remains a formula under D and Q, equality has numerical children,
and every numerical constructor has numerical children. The initial mode is
zero, used as the false value. The other values are Boolean. The integer case
is therefore

    numeric and (a == 0 or (a > 2 and a % 2)).

The list-arity test becomes `len(a) in (1, 2+numeric)` with the same explicit
diagonal-triple alternative as before. Induction on the input tree proves
equivalence with the depth-tracking relaxed validator.

## 4. Exact success-set preservation

For every JSON input in the idealized execution model without physical
resource limits, the old program accepts if and only if the new one accepts.
The type gate is identical; the public grammar preflight is equivalent by
sections 2 and 3; and the proof kernel and all subsequent transitions are
identical. An exception is rejection in both programs. This proof includes
malformed JSON values after decoding, not only canonical certificates.

It follows that every previously established soundness, completeness, and
native/iPRA interpretation result for the inherited certificate system is
retained. This is a preservation result for the unchanged theory, not a new
proof of its inherited arithmetic bridge or a new Lean verification.

## 5. Evidence and exact improvement

The complete modules are measured after `ast.unparse` plus one newline:

| Complete strict full Eq/Q/D checker | Tokens | AST nodes | Bytes | Gzip 9 |
|---|---:|---:|---:|---:|
| Inherited lexical gate | 383 | 442 | 870 | 507 |
| Scope reuse plus Boolean grammar mode | 377 | 433 | 860 | 508 |

All three primary coordinates decrease: 6 tokens, 9 AST nodes, and 10 bytes.
The informational gzip size increases by one byte. No diagnostic was shortened
and no source or validator was omitted from the count.

`reproduce.py` compares both complete programs on 68 fixtures under ordinary
and optimized Python (272 executions), and compares their grammar/scope
preflights on 9000 generated trees. The fixtures include used induction,
transport under both binders, capture attempts, invalid scope, forged majors,
forbidden compound induction, unused-prefix type attacks, and public Q shape.
All finite checks pass. The universal justification is the argument above.

This 860-byte result does not beat the separate 516-byte compact program,
which implements a different validation contract. The archive retains that
source for honest comparison.
