# A fixed rule permutation saves two universal history operations

The complete sparse Turing-machine compiler now has an **808-operation
universal polynomial**, **349 multiplications + 459 additions/subtractions**,
with **125 positive witnesses**, three positive program parameters and
exact degree **130394**. The corresponding certificate has
**728=322M+406A** operations and27 comparisons. Supplying the initial
history value gives **811=350M+461A**,126 positive witnesses,28 comparisons
and degree **5204**.

This is the same fixed U15,2 machine, state orientations, physical rules,
prefix code and paid ordinary-input convention as the
[810-operation parent](gpcp_sparse_tm_compiler.md). Only the order in which
its fixed rewrite rules are listed changes. The complete scalar source
is rebuilt for that order; this is not an asserted identity of old and
new packed witness tuples. The separate universal87 polynomial and75-operation
certificate frontier remain smaller.

## 1. The explicit table permutation

Keep the four copy tiles in their original order. For each of the53
rewrite rules `(a,b)`, encode its two nonempty words with the parent's
fixed prefix code and write its append map as

    (A,C,B,D) = (2^|a_bits|, value(a_bits),
                 2^|b_bits|, value(b_bits)).

Sort the rewrite rules in descending lexicographic order of `(A,B,C)`.
Stable sorting resolves any ties by the old order. This is fixed compiler
data, not a variable run-time test. Every old rewrite rule occurs exactly
once and no copy or rule is removed. The [source](gpcp_ordered_sparse_tm.py)
records the actual permutation of both rule indices and full tile indices,
and asserts equality of the physical tile arrays under that permutation.
The [receipt](gpcp_ordered_sparse_tm.json) contains the full default source.

For any new tile word `w`, replace each tile index by its recorded old
index to obtain `pi(w)`. Since each tile retains both literal words,

    sigma_new(w)=sigma_old(pi(w)),
    tau_new(w)=tau_old(pi(w)).

The inverse permutation gives the converse. Thus for every pair of
boundary words u,v, including the paid universal program/input frame,

    exists w != empty: sigma_new(w)v = u tau_new(w)
      iff
    exists z != empty: sigma_old(z)v = u tau_old(z).

The word's chronological sequence of physical rewrites is preserved.
The sparse-run and bracket-cut theorems therefore apply unchanged. This
argument does not reorder instructions *within* a computation; it only
renames the table's selectable instructions.

## 2. Fresh arithmetic composition and positive completeness

The source computes the affine append maps of the actual reordered table
and invokes the complete slope-class planner on those maps. It builds a
new raw history block, comparison list and positive witness list. The
already paid recoder, ordinary-input block morphism, fixed program frame
and terminal append source stay literal. The full unit projection is
then applied to the newly composed raw source. A same-map rewrite guard
is neither removed nor bypassed: no old-to-new polynomial identity is
used for this changed table.

On a zero, the complete arithmetic history gives a common tile word.
The preceding permutation maps it to a parent word with exactly the
same endpoints, so the parent universal theorem accepts the same ordinary
input. Conversely a parent accepting computation supplies the translated
new tile word. The complete history converse constructs fresh positive
selectors, selected products, packing geometry and native Pell witnesses
for that word. All duration, positivity and strong-norm requirements are
retained. No assumption that their old numerical values survive the
permutation is needed.

The initial state is still before its scanned cell. The code assignment
and the two64-bit physical input blocks do not change, nor do the three
positive fixed program parameters. Universality is asserted on the same
valid program slices as the parent. The represented machine must accept
exactly the same ordinary inputs under every permitted leading-zero
padding. All these interfaces are inherited with their paid source gates;
there is no new input encoding assumption.

## 3. Literal costs and exact degree

The default code is the parent's `sparse_tuned` code. The actual planner
still selects baselines128/128, eight exceptional slope-class products,
and `N=57+8+4=69`. Its raw history has

    H=574=236M+338A,

saving two additions relative to H576. The complete source therefore has

    certificate = H+154 = 728=322M+406A,
    polynomial  = H+234 = 808=349M+459A.

The fixed rule permutation changes opportunities for sharing the paid
selector-group sums and transport expressions. Its cost is established
by the actual source, not by treating sorting or any multiplication by a
fixed coefficient as free run-time arithmetic. Sorting occurs once while
constructing the fixed polynomial.

| Code / initial history value | Certificate | Polynomial | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|
|Sparse tuned / computed|728|808|125|130394|
|Sparse tuned / supplied|728|811|126|5204|
|Balanced / computed|733|813|125|130394|
|Balanced / supplied|733|816|126|5204|
|Older prefix tuned / computed|734|814|125|130394|
|Older prefix tuned / supplied|734|817|126|5204|

Each code choice uses its own literal sorted table and complete planner.
The exact-degree audit runs on every resulting source. The parent's
three main-norm cancellation identities remain literal, the other
homogeneous degrees propagate through the new DAG, and a nonzero
highest-form evaluation proves that the bound is attained. It is not
inferred solely from unchanged word lengths or tile count.

A bounded search evaluated4,164 distinct rule orders with the default
code and baselines128/128, then rescored the selected order with the full
planner. The simple descending `(A,B,C)` rule reproduces the winning
source without retaining a search log or a random permutation. No
optimality of that search, table, code or arithmetic schedule is asserted.

## 4. Executable audit

```sh
/tmp/diophantine-research-venv/bin/python gpcp_ordered_sparse_tm.py
```

The checker retains six actual complete ledgers and144 full source
identities, half on signed assignments. It verifies288 arbitrary word
permutation/append identities,144 positive paid input frames, and every
rewrite rule in three bracketed contexts plus accepting cleanup. The
word checks compare old and new physical words independently of the
arithmetic circuit. The arithmetic checks audit its literal register
order, M/A count and complete unit/residual polynomial identity.

Full positive native extensions follow from the component converse and
the explicit word bijection above. The finite examples do not claim to
materialize complete astronomical Pell witnesses or to establish machine
universality from bounded runs.

Author generation and fresh default replay pass. Independent full proof/source
review found no issues and added384 bidirectional physical-word permutation
checks across all three code assignments, including empty words.
