# A restricted arithmetic-expression reader

## Exact code and contract

The line version uses the following two lines in the complete standalone checker:

```python
p = input()
q = (p.strip('0123456789-[], ') or eval(p)).pop
```

The public certificate is the first line of input. Its parsed value must be a
list. The final list element is the claimed closed native formula, and the
remaining elements are the proof stack. Later lines are ignored, exactly as
in a conventional first-line input protocol. The entire first-line expression,
including portions constructing unused stack entries, is evaluated before
checking begins. A successful run prints `ACCEPT` and terminates normally;
all exceptions reject. This is a different input syntax, not the same set of
raw JSON documents as the source checker.

The whole-document variant instead uses:

```python
p = open(0).read()
q = (p.strip('0123456789-[], \n\r\t') or eval(p)).pop
```

Here all source characters are checked and the whole document must be one
Python expression. Both readers have the same image of successful values.
The line version is 377 significant tokens / 430 AST nodes / 671 normalized
UTF-8 bytes when composed with the nonnegative forbidden-slot exact-mask kernel. The
whole-document version is 382 / 434 / 684. These measurements include the
entire source, including the reader, inference engine, and acceptance output.
The corresponding exact JSON checker is 383 / 438 / 691.

## Restricted evaluation theorem

**Theorem.** If either reader assigns a value to `q`, then `q` is the bound
`pop` method of a finite Python list whose recursively occurring values are
only exact Python integers and lists. Conversely, every finite list of such
trees has a source spelling accepted by either reader. No source-level name,
function call, attribute access, import, assignment, string literal, or
comprehension can be evaluated by either reader.

**Proof.** First consider the character test. `str.strip(S)` deletes a maximal
prefix and suffix consisting of characters from `S`. Its result is empty if
and only if every character in the string lies in `S`. If a disallowed
character occurs, the left side of `or` is a nonempty string. Short-circuit
evaluation does not call `eval`; access to the nonexistent string attribute
`pop` raises an exception. Thus `eval` is reached only after the entire input
expression has passed the character test.

The remaining tokens can only be decimal integer literals, minus signs,
square brackets, commas, and whitespace. In particular there are no
identifier characters, parentheses, quotes, attribute dots, braces, colons,
assignment signs, comparison signs, stars, slashes, or other operator tokens.
This excludes identifiers (including Python keywords and built-in names),
calls, imports, assignments, lambdas, strings, comprehensions, dictionary and
set literals, slicing, exponentiation, and multiplication. Unicode digits
are not in the allowed set. Unsupported decimal spellings, unmatched
brackets, and other syntactic failures cause rejection.

For successfully evaluated ordinary expressions, use structural induction
on the expression syntax. A decimal literal is an exact integer. A list
display contains ordinary expressions separated by commas; its successful
value is a list of their values. Unary minus can succeed only on an integer,
because lists do not implement numerical negation. Binary minus likewise
can succeed only on integers; it produces an integer. A subscript can
succeed only when its target is a list and its index is an integer. Its
result is an existing element of that list and therefore remains an integer
or list. Repeated subscripts and nested arithmetic follow the same argument.

There are two uses of comma worth separating from list displays. A comma in
a subscript constructs a tuple index. A built-in list rejects a tuple index,
so this cannot occur in a successful subscript. A comma at the top level
constructs a tuple of expression values. It has no `pop` attribute, so it
cannot result in a successful reader. Without parentheses, tuple values
cannot occur as ordinary list elements or as the target of a following
subscript. Consequently successful access to `.pop` forces the entire
result to be a list of exact integer/list trees. No object with user-defined
methods can be constructed from this syntax, and no input-level name or call
is reachable even though the host `eval` has its ordinary environment.

For the converse, recursively print each integer in decimal with an optional
leading minus, and each list with square brackets and comma-separated
printed elements. This is an allowed Python expression with exactly the
required value, and the top list has a bound `pop` method. The construction
is primitive recursive on the finite tree coding. All successful evaluation
steps operate on finite syntax and finite values. As with the JSON baseline,
mathematical completeness uses the usual ideal finite-resource convention;
fixed interpreter recursion, memory, and integer-digit limits are not
mathematical proof-system bounds. This proves the theorem.

## Examples and nonexamples

The expressions `[0,[1],[-2]]`, `[1-1,[2-1],[0-2]]`, and
`[[0,[1],[-2]]][0]` produce the same tree. The new syntax permits redundant
arithmetic and list indexing as concrete input notation. The inference
engine sees only the resulting tree.

`[True]`, `[1.0]`, `[0x1]`, `[1e0]`, `[1_0]`, `open(0)`,
`__import__('os')`, and `().__class__` fail the character test before `eval`.
The strings `1,2`, `[],`, and `[1][0,0]` use only permitted characters, but
cannot supply the required top-level list: the first two produce tuples and
the third attempts a tuple subscript. `[1][1]` and `[]-[]` fail at evaluation.

## Transfer to the exact iPRA checker

Let `K(P)` be the unchanged exact-mask kernel applied to a finite list `P` of
integer/list trees. The JSON checker reads `P`, checks its whole alphabet,
then invokes `K(P)`. The expression checker obtains exactly the same class
of `P` values by the theorem above, with no separate alphabet traversal.
Its canonical closed goal validator and every inference instruction are
literally unchanged. Therefore a successful expression certificate gives a
successful integer/list certificate for the exact JSON checker. Conversely,
the canonical expression spelling of any successful integer/list certificate
is successful for the expression checker.

This proves equality of accepted goal sets and transfers the exact goal
grammar, soundness, canonical theorem completeness, and inherited whole-domain
bi-interpretation to the new reader. It asserts neither identical sets of raw
input bytes nor a new arithmetic axiom basis. The separate exact-mask theorem
is essential: this reader does not repair any formula-padding aliases by
itself. With the broader sorted-goal checkers the same reader preserves their
weaker per-spelling completeness contract instead.

## Verification evidence

`verify_expression_reader.py` checks 3,000 canonical and alternative spellings
of randomly generated integer/list values, rejects adversarial reader strings,
and runs the complete exact checker in ordinary and optimized Python on
canonical, arithmetic, and indexing spellings of positive and negative proof
fixtures. The receipt records the exact process count and all failures.
These finite checks support the implementation; the theorem above supplies
the universal input-language argument. No Lean/Rocq verification is claimed.
