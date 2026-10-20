# Logical calibration required by an unchanged-source reduction

The new 219 release at ProveIt commit
`26d5de6d21fa354d50e0b84fe851c289925b8d72` changes the implementation of
four equality tests while retaining the calibrated native calculus. Its
`report/sections/calibration.tex` states the internal equivalence

\[
\operatorname{Halt}(M_{219},\mathrm{blank})
\quad\longleftrightarrow\quad
\exists d\;\operatorname{Proof}_{\mathrm{ZFC}}(d,\bot).
\]

The inherited comparison uses effective transformations of finite
refutations, not an assumption of soundness or a set model of all of ZFC.
The source interfaces retain the formula codes, exceptional code-zero
convention, equality rows, arithmetic freshness gates, complete seed-K
bundle, retained theorem stack, and contradiction code 1. The equality
macro is total on every natural input and clears the same two scratch
registers, so exceptional and coincident numerical codes stay within the
original calibration.

For a further change that retains `sites219.json` exactly, the logical
part needs no new theorem about T, explosion, G/H, or a weakened set theory.
It is enough to prove the exact binary table implements that source and
to establish its blank startup. Specifically:

1. Every guarded primitive interface must be total on arbitrary natural
   logical registers, arbitrary permitted gap, and every finite nonempty
   spare list. It must return a complete valid frame with the same source
   outcome, take positive finite time, and have no intermediate machine
   halt unless the source primitive halts.
2. A separate literal blank-tape simulation must reach the required source
   entry and logical register vector. Equality of the physical gap, spare
   count, and tape support with the predecessor is unnecessary, but every
   field in the new frame must be checked.
3. The transition table, state count, start state, terminal outcome, and
   canonical relabeling must describe the exact bytes under review.

Concatenation of the finite primitive simulations then gives the two
directions of blank-halting equivalence. Positive duration prevents an
infinite source trace from corresponding to only finitely many machine
steps. Composing with the pinned finite-refutation translations gives,
inside ZFC,

\[
\neg\operatorname{Halt}(M,\mathrm{blank})
\quad\longleftrightarrow\quad \operatorname{Con}(\mathrm{ZFC}).
\]

These requirements do not assume `Con(ZFC)`. They also do not assert
unconditional nonhalting or minimality of the state count. The inherited
and new endpoint proof boundary is an ordinary mathematical argument,
formalizable in ZFC and supported by executable symbolic certificates;
it should not be described as a newly compiled Rocq or Lean theorem for
the exact final machine bytes unless such a theorem is actually supplied.
