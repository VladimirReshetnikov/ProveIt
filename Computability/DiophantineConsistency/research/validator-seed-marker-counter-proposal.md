# A bounded marker counter for internal proof interpretation

27 October 2026. Mathematical proposal only. No new interpretation law,
proof transport, cache plan, overlay or compiler run is certified here.
The existing `InternalInterpretation.Good` contract remains unchanged.

## The obstruction and the proposed invariant

The tagged domain with marker `&j` is
`d(j) := (&j ∈ #0)`. Its shift is d(j+1), not d(j). The existing
shift-fixed interpretation theorem therefore does not apply. A proof of
guarded comprehension with arbitrary internal matrices does not by itself
remove this obstruction.

Use a represented family of interpretation parameters P(j), with this
domain and corresponding atom meanings. Each member is well typed, and
shifting each component of P(j) gives that component of P(j+1). For the
first tagged relativization the atoms retain raw equality and membership;
later quotient meanings need their own checked family instance.

Write I(j,p) for the existing raw `interp P(j) p` construction, S(j,s)
for its image on a source sequent, and

```text
E(j) = ¬Empty(&j)
C(j) = { ¬d(j)(&i) : i < j }.
```

The proposed transport statement is

```text
Derivation T der →
∀ j > der, Derivable U ( S(j,fstIdx der) ∪ {E(j)} ∪ C(j) ).
```

The source proof code bounds every source term and free label used in its
subderivations. This must be proved using the actual coding inequalities;
it is a separate obligation, not an assumption licensed by this proposal.
The strict j>der bound reserves the marker above those source labels. The
side set is canonical: its length and marker index are both j.

The inspected Foundation code already proves `var_lt_qqFvar`,
`t_lt_exsIntro`, `p_lt_axm`, and all strict child-code bounds, including
`s_lt_allIntro` and `d_lt_shiftRule`. Thus the EXS label bound has the
concrete chain `i < ^&i = t < exsIntro ... < j`. The combined invariant
and all uses of those bounds remain to be formalized.

The actual axiom-image resource must have the corresponding form: for
each internally recognized T-axiom p, and each j above its code, U derives
`{I(j,p),E(j)} ∪ C(j)`. This is not presently proved for ZF. Guarded
comprehension, Collection and quotient/WF axiom images remain necessary.

## Bounded induction rather than an unbounded universal motive

An unbounded `∀j ∃proof` induction motive would exceed the Sigma1
interface. The already checked `ModelCodedProofRenaming` suggests a precise
alternative. Fix an internal total budget B and use

```text
Derivation T der →
∀ j ≤ B, der < j → der+j ≤ B →
  Derivable U ( S(j,fstIdx der) ∪ {E(j)} ∪ C(j) ).
```

The only new universal counter quantifier is bounded. If the interpretation,
guard and side-set graphs are total Sigma1 functions, this predicate should
have the Sigma1 definition required by genuine IΣ1 order induction.
That definability proof must be checked, including every side condition.

At the outer endpoint choose j=der+1 and B=der+(der+1). The ten derivation
cases then use these counter changes:

| Source rule | Child marker counter | Reason |
|---|---|---|
| ALL | j+1 | Opening the target quantifier shifts the marker too |
| SHIFT | j−1 | Shifting the child target restores marker j |
| AND, OR, EXS, WK, CUT | j | The marker remains fixed in these cases |
| Logical initial, verum, theory axiom | no recursive call | Direct proof or actual axiom image |

For ALL, child<der implies child+(j+1)≤der+j. It also gives child<j+1.
For SHIFT, der<j and child<der imply j>0 and child<j−1; its budget
decreases. The coding bounds and discrete-order steps must be proved in
the internal model. This argument is patterned on the existing bounded
renaming proof, not on standard-Nat induction over internal proof codes.

## Required syntax and set laws

Prove new family laws without weakening or invoking `Good.domShift`:

```text
shift I(j,p) = I(j+1,shift p)
free I(j,p) = I(j+1,free p)
shift E(j) = E(j+1)
setShift S(j,s) = S(j+1,setShift s)
C(j+1) = { ¬d(j+1)(&0) } ∪ setShift C(j).
```

The last equation follows by splitting i<j+1 into i=0 and i=k+1,
with k<j. Here each domain formula shifts from d(j) to d(j+1).
The ordinary negation and bound-variable substitution laws should need
well-typed components, without shift-fixed components. These weaker
contracts require separate proofs and complete dependency review.

For ALL, the free domain guard supplies the missing i=0 member of C(j+1);
the rest is exactly the shifted parent side set. For SHIFT, shift C(j−1)
is a subset of C(j). The empty guard obeys the same family shift. EXS
requires its free witness label to be below j, established from actual
source-term/proof coding bounds. CUT uses the same j in both branches and
the checked interpretation/negation law. No marker-preserving free
renaming theorem is silently assumed.

## Discharging the side formulas at falsum

For a refutation the interpreted source sequent is just falsum. Define
the candidate residual sequent R(j)={falsum,E(j)}∪C(j). Its family law is

```text
R(j+1) = { free (¬d(j)) } ∪ setShift R(j).
```

Consequently an actual derivation of R(j+1) can be generalized at the
opened variable to a derivation of `{∀x ¬d(j)(x)} ∪ R(j)`. Cut against
an actual U-proof of `∃x d(j)(x)` to obtain R(j). The accepted source
theorem `ValidatorSeedSourceBasis222.tagged_nonempty` supplies this
nonempty-tag proof for every internally typed marker term, with no Empty
premise. This use still needs its raw `Derivable` certificate conversion.

As in `InternalRelativization.derivable_of_domSet`, eliminate an arbitrary
internal initial length N using the Sigma1 invariant

```text
∃ j, j+k=N ∧ Derivable U R(j),   for k≤N.
```

At k=N, j=0 and C(0) is empty. Removing the redundant falsum gives a proof
of ¬Empty(&0). Generalize that remaining free variable and cut against the
accepted actual source proof `empty_object : U ⊢ ∃x Empty(x)`. The exact
`emptyBody.free` identity and theory/Derivable conversions must be retained.
This closes only the conditional interpretation transport once its actual
axiom-image hypotheses are supplied.

## Review obligations before implementation

1. Check the actual parent/child, formula and free-label code inequalities.
2. Prove total fixed graphs and all family substitution/shift/free laws.
3. Check Sigma1 definability of the bounded proof induction motive.
4. Handle every logical/theory rule at the stated sequent, including EXS
   witness bounds and both CUT branches.
5. Prove the simultaneous counter/domain discharge over arbitrary internal N.
6. Supply genuine tagged and quotient/WF axiom images for the actual source
   theories; the generic transport resource does not discharge these.
7. Select and authenticate an exact current-source cache closure, then review
   final sources and drivers before any future compiler run.

The side-set and bounded-counter proposal is based on inspected local
implementations of `InternalInterpretation`,
`InternalRelativization` (especially its discharge section),
`ModelCodedProofRenaming`, `ValidatorSeedSourceBasis222`, and the Foundation
term/proof constructor inequalities. The accompanying
source-pin JSON records those inspected bytes. It does not certify that
this proposal has passed a compiler or that the HA endpoint is proved.
