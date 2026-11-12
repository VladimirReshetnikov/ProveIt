# Independent audit of native_tuple.py

Files reviewed:

- `work/math/native656.py` (control)
- `work/math/native_tuple.py` (candidate)

The public-goal validator is byte-for-byte unchanged. The active introduction
mode `len(a) % 2 == u` is unchanged; in particular the distinct flags `u=0`
and `u=[]` retain their progress/case roles for an equation.

## Exact source changes

1. `[s,u] if s else [t]*3` becomes `s and [s,u] or [t]*3`.
2. The two major/target comparisons become a comparison of pairs.
3. `C and R or a` becomes `(a,R)[C]`, where R is `i(t,s)`.
4. The integer decrement `k-1` becomes `~-k`.

The first rewrite is exact on standard JSON values because `[s,u]` is always
nonempty. The fourth is exact because k starts at integer zero and is only
decremented.

## Evaluation phase

The validator flag v is set to zero before a packet is read. The common h
assignment, including the recursive major proof and any introduction update
of a, happens first in both sources. Each checker call has a local k, so the
recursive major proof cannot modify the caller's floor. All opener calls in
the comparison and the tuple replacement precede `k := ~-k` and use the same
floor. Context extension allocates a new list and never mutates a parent's
context.

## Comparison and false-result lemmas

At formula-root depth zero, a successful opener on a scalar returns either
a finite negative number preserved by the interval test or zero. It does not
inspect its image there. On a list it returns a newly built list with the
same root arity. Thus, if R=i(t,s) and T=i(t,u) both succeed and R is false,
then R=T (both empty lists or both zero).

The candidate condition C is true exactly when the old major comparison and
target comparison are both true, provided the candidate's eager evaluations
succeed. This is immediate on integer/list trees. It also holds for standard
JSON values accepted by Python's decoder, including its nonfinite numeric
extensions, for the following reason. Induction on any finite successful
opener execution shows that its output is a list tree with finite numeric
leaves: a retained scalar lies between finite k and d, and every other scalar
branch returns zero or another successful opener result. NaN and infinities
cannot be retained. Hence the target T has reflexive equality, so tuple
identity shortcuts cannot convert a false scalar target comparison to true.
The expected major is a fresh nonempty list, so the tuple comparison invokes
the same major list equality as the control. Equality of ordinary JSON
builtins is symmetric, so reversing the target-comparison operand order is
harmless. Arbitrary Python objects with overloaded methods are outside the
input interface.

If C is false both goal selectors choose a. If C is true, a=T. When R is
true both choose R; when R is false the previous lemma gives R=T=a, so the
old fallback also equals R. Therefore the selected goals agree on every
successful new execution.

## Successful-trace inclusion

The candidate eagerly computes R and T, even when the control might skip
them. These computations are pure and consume no proof instruction. On a
successful candidate execution all operations used by the old execution are
defined, the selected goal agrees, and the remaining context/floor updates
agree. Induction on the finite successful execution tree proves acceptance
by the control with the same consumed instruction stream and common checker
entry states. This is an idealized unbounded finite-execution statement;
ordinary runtime limits remain ordinary resource limits.

No converse for arbitrary raw certificates is claimed. An unused field can
make a new eager opening fail even when the control would have skipped it.

## Canonical completeness

For canonical terms, numerical nodes have arity one or three. A formula-root
opening of a canonical numerical field therefore stays at even depth and
does not inspect its image. It terminates. Genuine elimination packets
already require the selected opening in their control proof; a valid source
image also makes opening total on arbitrary finite trees. Standardize inert
fields to zero in introduction and D-opening packets. This yields a candidate
certificate for every canonically compiled control derivation, without
changing the public goal or the arithmetic rule inventory.

## Contract precision

The initial goal validator checks native canonical Eq/D syntax, not every
item of the certificate. The candidate must not be described as globally
rejecting every noninteger certificate leaf: inactive or semantically erased
JSON data may remain accepted, as in the control. Its retained public grammar
check and the inherited sorted interpretation are the proper claims.

Verdict: the candidate preserves soundness by successful-trace inclusion and
preserves the canonical native theorem set. No new arithmetic axiom deletion
or absolute minimality claim follows from the size reduction.
