# Conditional positive transport from scalar parent data

[`Model69Outer.lean`](Model69Outer.lean) composes the independently audited
[rank-growth](../../reviews/thirteen-model-parent-growth-independent-audit/README.md)
and [positive-transport](../../reviews/thirteen-model-parent-transport-independent-audit/README.md)
lemmas with `ArithmeticPellFirstIndex.scalar_window` in an arbitrary `IΣ₁`
model. Given positive model naturals `beta,J,F,alpha,z,w,s`, arbitrary
model naturals `K,MC,MF,u,count`, and `MC<beta`, `MF<2*beta`, define

```
q = beta*J+1
R = ((q-1)*(q-F)+alpha)*(q²-1)+(MC+q*MF)*J
C = q-F-alpha.
```

The theorem assumes the parent additive transport factor,

```
(K+w)*q+q = (K+w)*(F+alpha)+F+z*(q-1)+1,
```

and the supplied estimates `q=Exp.exp u`, `w*q=Exp.exp R` and
`3*u+2≤count≤R`. It derives `C>0` and a model-natural `G>0` satisfying
`beta*J ∣ G` and `(K+w)*C=F+G`. In particular it derives `F<q` and `q≤w`
from those inputs rather than assuming them separately.

This is a **conditional scalar model lemma**, not an actual-zero theorem.
The parent equation, powers and population bounds still need to be extracted
from the exact 2011 positive zero, and the rank phase `R%4=3`, the new
13-coordinate literal binding and both model zero directions remain
separate. Nothing here calibrates the distinct phase-split2471 tuple or proves
an internal iPRA equivalence.

## Replay and exploratory failure

[`replay.py`](replay.py) checks and reruns the two independent parent audits
before and after compiling this suffix on both corresponding 70-source
providers. It pins source, compiler and audit inputs, checks direct imports,
uses `-M4000 -j1`, and records actual child exits and object hashes. Session
72974 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_PARENT_OUTER 5690d4452611aea1e96809c73c549bc46dbfde87ddcaa5decd6386b5b4edb8c9`.
The [receipt](replay-receipt.json) and [terminal observation](terminal-observation.json)
record matching objects and successful child and outer exits. Both copies
report `[propext, Classical.choice, Quot.sound]`, without warnings or
`sorryAx`. Lean metatheory axioms are not object-level iPRA axioms. The
suffix has not yet been independently audited; package-transitive and
dynamic ancestry and the original Foundation wrapper's unobserved exit remain
inherited.

The first exploratory composition session 32833 actually exited 1 after a
missing let-unfold and printed `sorryAx`; it is not proof evidence. The
corrected exploratory session 38119 actually exited 0 without warnings and was
then reproduced in the paired run above.
