# Measuring compiler syntax without constructing its trees

[`RepresentationSize.lean`](Lean/DiophantineConsistency/RepresentationSize.lean)
proves count and depth recurrences for the supplied arithmetic compiler.
`Expr.splitSize` counts both natural-expression trees produced when an
integer residual is split into a positive and a negative side:

```
S(constant)=S(variable)=2
S(p+q)=S(p-q)=2+S(p)+S(q)
S(p*q)=6+2*S(p)+2*S(q).
```

Lean proves these counts equal the actual compiler node counts, independently
of variable names and coefficient magnitudes. Renaming preserves them.
The depth estimates are also structural: splitting at most doubles depth,
and a natural expression of depth `h` has at most `2^(h+1)-1` nodes.

For a supplied representation with at most `m` source witnesses and integer
residual depth at most `h`, `rawQuarticVariables_le` gives

```
rawQuarticVariables + 1 <= m + 2^(2*h+2).
```

The compacted quartic has no more variables than this raw quartic. These are
proved upper bounds, not measured exact counts. They can be propagated
alongside compiler constructors without evaluating the large syntax fields.

[`GraphSizeBounds.lean`](Lean/DiophantineConsistency/GraphSizeBounds.lean)
proves substitution-depth bounds and propagation of the invariant
`Rep.Thin C r`, meaning `r.depth <= 6*r.witnessCount+C`, through the actual
graph constructors. Fixed polynomial blocks need their own depth bounds;
they are not charged as if they were atomic variables.

The consolidated checks cover both modules and audit sixteen declarations;
only Lean's standard axioms occur.

`NativeEnumerationSize` certifies the actual fixed formula/stack blocks.
`NativeEnumeratorBounds` then proves that the actual 1,742-witness enumerator
step has residual depth at most 10,964. The option-valued step wrapper has
exactly 1,752 witnesses. `IterationSize` identifies the transition relation
used by the existing bounded trace: it has exactly 1,782 witnesses and depth
at most 11,204. The wrappers' extra witnesses are included explicitly.
Their separate consolidated checks audit eighteen additional declarations,
using only the standard axioms.

Closing the outer bounded universal quantifier and the whole native quartic
bound is a separate step. A conservative upper bound must not be confused
with an expanded evaluator count or a proof that the resulting equation is
smaller than another candidate.
