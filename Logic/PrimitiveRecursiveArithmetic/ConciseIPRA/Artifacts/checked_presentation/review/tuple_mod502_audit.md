# Independent audit of tuple_mod502.py

Compared files:

- `work/frontier/base506.py`
- `work/frontier/tuple_mod502.py`

The modifications are the tuple-indexed goal selector and the remainder
formula used for the introduced hypothesis. The rest of the checked source
is unchanged.

## 1. Tuple selector after delayed dispatch

At the relevant statement, the common previous line has already evaluated
the major proof and assigned `h`; in an introduction it has also reassigned
`a`. This changes neither the proof of the selector rewrite nor its scope
floor. The caller's `k` is a local argument. Recursive calls of `c(m,g,k)`
cannot mutate it. The shared default context is never mutated: context
extension is `g + [...]`.

Write C for `(m,a)==(s and [s,u] or [t]*3, i(t,u))` and R for `i(t,s)`.
All these opener calls precede the `k := ~-k` update. Thus they use the same
scope floor in both programs.

For finite integer/list trees the opener is pure. Its formula-root output
has the same root arity as its input if the input is a list. At an integer
root and depth zero its output is independent of the image: either that
negative integer or zero. Therefore, if R and i(t,u) terminate and either is
false in Python, they are equal (both [] or both zero).

If C is false, `(a,R)[C]` and `C and R or a` both select a. If C is true,
then a=i(t,u). For true R both select R, and for false R the previous lemma
gives R=a. The selected goals are equal on every successful new execution.
The new expression additionally evaluates R when C is false. This can
reject additional certificates; it does not add a successful trace when
the remainder selector is left unchanged.

Canonical completeness survives: numerical fields have only odd list
arities (one and three), so a formula-root opening remains at even depth
and cannot inspect the image. Genuine elimination packets already had a
successful selected opening; valid numerical images also make the opener
total on all finite integer/list trees. Inert introduction and opening
fields can be standardized to zero.

## 2. The remainder selector

For meaningful arities n=1,2,3, both `~n % 2` and `3 % n` have values
0,1,0. For n=0 the new program rejects by division by zero. For every n>=4
the inherited formula decoder treats the formula as administrative truth.
For odd n>=5 the mode changes from zero to the fresh parameter, but this is
a truth hypothesis and cannot add a meaningful premise. Computation-supply
steps remain substitution instances of the same computation equation under
either image. At nonzero major m neither arity expression is evaluated.

This is a semantic soundness argument, not successful-trace inclusion in
base506.py on all integer/list certificates. Exact trace inclusion applies
only to the tuple transformation, or after restricting every relevant arity
to 1,2,3. A final report must not silently promote that intermediate
property to a property of the composed program.

## 3. Contract and status

The argument uses the inherited integer/list certificate contract and
guarded public Eq/D goal language. The compact program itself does not
validate that contract. A strict standalone checker must include and count
the validator. Both the inherited bridge to iPRA and the surplus-arity
semantics remain assumptions of this implementation audit. Finite tests do
not replace those mathematical obligations. No new primitive mathematical
axiom or inference rule has been removed.

Verdict: the two modifications compose correctly under those conditions.
