# Scope obstacle for fusing normalization into the arity opener

The current arity codec uses innermost slot indices. It increments depth by `5-r` at an r-child array, creating dummy slots below successor and in the counter/initializer of an iterator. Its opener replaces a single exposed outermost slot by a closed numerical image.

This opener cannot naively serve as a bottom-up normalizer. A local iterator contraction removes its innermost state/dummy slot, which rebases every surrounding slot in its initializer/body. Merely returning the recursive result for the initializer is incorrect.

For example the uniform-zero public encoding of

    D_{x,y}(I(0,x;u.u) = x)

is

    [[[1,7,3],5]]

The D matrix is at depth 4 and equation endpoints at depth 7. The outer variable x is code 5 there. Under the iterator's extra slot it is code 7. Contracting the zero iterator must therefore turn its initializer code 7 into code 5. A naive `counter==zero ? initializer : ...` returns 7; in the resulting endpoint at depth 7 this is an exposed hole, not x.

A correct fused normalizer needs explicit rebasing or an environment invariant that proves the necessary substitution and composition laws. Normalization only at top-level root terms (depth 3, with no surrounding bound slots) avoids this particular example, because the existing opener can discharge the iterator's outermost slot there, but it does not automatically yield a complete calculus for formula and term bodies under binders.

There is no mathematical obstruction from a numerical-zero transport source if the uniform-zero codec is used: canonical zero is scalar 1, so it remains true-valued in source dispatch. If a different calculus really forbids the normalized literal zero as a transport source, an open anchor I(b,0;u.0), provably equal to zero by equation induction, can replace the erased closed zero-redex anchor; a fresh b can be introduced and discharged by the theorem D(0=0).

Guarded atomic matrices are generally not preserved by full normalization. A replacement checker must either validate a new public contract or use the native witness-selected introduction and its established zero-witness repair. The existing full-normalization theorem does not itself justify a new eager arity traversal without the scope and coherence proof.
