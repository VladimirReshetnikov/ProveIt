# Successor-only uniqueness and the 57-node predecessor

Pinned source audited: the incoming `ipra_zero_test_split_2026-11-12` package's `reference/predecessor57_detailed.tex`, in the full checkout research directory supplied by the parent.

## Established transfer

The SU theory has ordinary intuitionistic logic with actual equality, the scalar computation equations, numerical coverage, separation, and the contextual rule

`f(Sz) = S(f(z)) / f(t) = I(t,f(0);u.Su)`.

The current article already proves contextual zero-equation induction (ZI) from SU. It also proves the commutative-monoid identities for addition. These may be used without introducing equation induction.

Let `C(v,a,b)=I(v,a;u.b)`, `Z(v)=C(v,1,0)`, `sg(v)=C(v,0,1)`, and `N(v)=I(v,0;u.Z(u))`. Coverage gives `Z(v),sg(v),N(v) ∈ {0,1}` (for N, use its zero and successor computations). A useful explicit characteristic is

`chi(a,b) = C(b, sg(a), Z(N(a)))`.

If `a ∈ {0,1,2}` and `b ∈ {0,1}`, finite cases prove `chi(a,b)=0 iff a=b`. No predecessor, injectivity, or arbitrary equality reflection is needed: the only N-values used are its computations at 0,1,2. Therefore every contextual induction on an equality `a(n)=b(n)` with those guaranteed finite ranges reduces to ZI on `chi(a(n),b(n))=0`.

Consequently the predecessor57 proof's finite-valued steps transfer to SU:

* parity scaling `N(2n)=0` by ZI directly;
* parity scaling `N(3n)=N(n)` by the finite characteristic;
* the 3-state range of `M(n)=I(n,0;v.J(v))`, where `J(v)=I(v,2;w.Z(w))`, by coverage and computation;
* the crucial finite invariant `M(R(n))=N(n)`, where `R(n)=I(n,0;u.S(C(M(u),Su,u)))`, by ZI via chi;
* the resulting step equation `R(Sn)=R(n)+1+Z(N(n))` and the algebraic two-step law `R(n+2)=R(n)+3`, by finite cases and the SU-derived addition laws.

## First unresolved unbounded step

The next existing step is `R(2n)=3n`. Its two sides share update `v -> v+3` and base 0. This is a UR instance for a three-successor update, not an SU instance. Neither side is restricted to a finite range, and no actual-equality characteristic is yet available. Reusing the manuscript's literal-equation induction here would assume the desired conclusion of the SU research program.

Even if this one scaling identity were recovered, the later proof contains additional unresolved uses:

1. the unbounded triple equation `R(3n)+N(n)=3R(n)`;
2. arbitrary-body rotation `I(Sy,a;h)=I(y,h(a);h)`;
3. fusion `I(y,3a;H)=3I(y,a;H)`;
4. the saturated-iteration shift `W(St,Sm)=S W(t,m)`;
5. extensionality for the two final pointwise-equal iterator updates.

Some individual downstream equations might have alternative SU proofs; this audit does not establish impossibility. It establishes that the supplied proof cannot simply be recast as SU plus Boolean reasoning. The point requiring a genuinely new unbounded argument is already `R(2n)=3n`, before the comparator and final predecessor.

## Status

No derivation of the full predecessor, actual-equality reflection, or arbitrary equation induction from SU was found. No countermodel to SU was constructed. The known two-fiber zero-induction countermodel refutes SU itself and cannot settle its strength. The new result from this agent is instead the written raw-variable-substitution obstruction in `raw_variable_substitution_obstruction.tex`.
