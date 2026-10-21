# Omit-zero on the dominated continuation source

This is an ordinary compiler argument applying Source151's successful-MP
change to Source149's exact common-input command semantics, inherited unchanged
by Source152's three closed rotations and contextual fold. It is a semantic
change, not equality of command traces. No modified Lean theorem is claimed.

The work tuple is `(t,S,d,h)`. Write `P` for native Cantor pairing, `I` for
native implication, and `F=1`. In the accepted dominated source, MP with field
`z` sets `B=d+z`, compares the cached code with `I(t,B)`, and on success returns
`(B,P(0,S),B,0)`. The variant returns `(B,S,B,0)`. Failure still returns
`(0,S,B,0)`. All other commands are unchanged.

The exact source edit deletes the closed19-leaf PUSH at `1111110` and promotes
its closed7-leaf COPY sibling `1111111` to `111111`. The physical change is
only `164/1: 1 R98 → 1 R114`. The source checker verifies the entire retained
ordered word, both complete control-flow constructions with the deleted block
bypassed, all internal decoder states at their expected corresponding paths,
and every retained leaf's literal action. It does not infer runtime soundness
from a state count.

## Soundness

The original invariant requires current code, cached code, and every stack
head to be theorems of the dominated calculus. Successful MP applies its exact
numerical rule and now leaves an already sound stack unchanged. Failure,
DROP, NIP, and AX retain their established invariant preservation. The additive
counter is not assumed to encode a theorem. A halt still requires theorem
cache`F` at a NIP test.

AX uses the actual wire order `AX(c,z,y,x)` with
`U=d+z`, `A=U+x`, `B=h+y`, `C=c`. It pushes seven retained rows, the dominated
rho8 row, `Q_U h`, and the old top, and clears `d,h`. The gated current result
is0 when `c=A` or `c=B`. Thus its raw row instances still obey `U≤A`, and no
axiom gate or numerical parameter restriction is changed by omitting PUSH.

## Strong compiler repair

Retain the strong block contract: from every `(t,S,0,0)`, a compiled derivation
of`G` halts or returns `(G,S,0,0)`. Arbitrary initial `t,S` are permitted in
this contract; global soundness separately uses the theoremhood invariant.

The existing discard block begins `MP(1)` with cache0. It necessarily fails,
because `I(t,1)>0` for every natural`t`; native code0 does not create an
exception. Therefore discard, leaf-selection, and generalization blocks do
not depend on the changed successful-MP branch.

The old MP block first arranges its hypotheses using their strong contracts
and DROP/NIP, then executes `MP(G)` with additive counter0. Successful execution
now gives `(G,S,G,0)`. Replace only its cleanup tail by

```
AX(G,0,0,0); NIP(0)^10; DROP(0); NIP(0)
```

This deletes the last NIP from the original compiler tail. In this reset AX,
`U=A=C=G`, so the exact gate returns0, including when`G=0`. Let`L` denote its
nine generated stack entries. The nonhalting trace is

```
(G,S,G,0)
  → (0,L::G::S,0,0)
  → (0,S,0,G)       after ten NIPs
  → (G,0::S,0,G)    after DROP
  → (G,S,0,0)      after NIP.
```

Any earlier test of cache`F` halts and satisfies the disjunctive contract.
In particular `G=F` halts at the final NIP rather than returning. This handles
all natural conclusions and preserves the surrounding arbitrary stack.
Induction on the derivation establishes the modified strong block contract.

Finite wire packing is unchanged. The cofinal reset family from Source149
prepends `AX(0,1,1,Y)` to a fixed compiled refutation and has encodings
`P(3,P(1,P(1,P(Y,R))))≥Y`. It still resets counter and cache, produces only
permitted dominated rows, and enters the repaired strong block. Candidate
draining and enumeration are unchanged. Thus the command-level halt/refutation
equivalence transfers with this one compiler-tail deletion.

## Physical evidence and remaining boundary

The canonical217 parent has a fresh full arbitrary-natural runtime receipt.
The composition reruns no inherited wrapper: it checks the finite source and
decoder relation, then reconstructs all312,617 transitions of the parent's
frozen blank-start trace. Both tables have the same action throughout that
trace; changed row164/1 is absent. The complete endpoint, including all277 one
cells, is unchanged.

The variant remains217 states,434 rows,203 distinct source DAG nodes,4732
primitive occurrences and6151 guarded cases. All167 physical decoder states
remain represented. A full primitive replay for this shortened source was
not performed. Its two bounded fold searches do not turn the variant into
an accepted216-state machine and do not establish a state lower bound.

The exact upstream proof texts are retained in `theory/`: Source151 gives the
omit-zero repair, while Source149 gives the common-input AX equations and
cofinal strong compiler. Source152 changes only closed source associations
and their physical implementation.
