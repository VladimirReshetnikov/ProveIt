# Euclidean division and the literal div/mod quartic in internal omega

`ObjectDivision.division_exists` and `division_unique` establish the
Euclidean relation `n=q*d+r` and `r<d` for every internal natural numerator
and positive denominator. They apply in arbitrary `ZFAxioms` models,
including those with nonstandard naturals.

Existence uses a displayed set-theory formula and `omega_ind`, with the
denominator retained as a parameter. At successor steps the remainder
increments, or wraps to zero when its successor equals the denominator.
Uniqueness uses strict-order difference certificates: unequal quotients
would force the same numerator to be strictly less than itself. It does
not rely on an external well-ordering of the model's carrier.

The semantic operation `divmod` selects the unique pair and uses `(0,n)`
at denominator zero. `divmod_cast` proves exact compatibility with the
actual external `Nat.div`/`Nat.mod` convention on numeral inputs. The
displayed positive-denominator totality sentence has an unconditional
derivation in the existing sealed ZFC calculus.

`ObjectDivModSyntax` binds this arithmetic to the actual two residual rows
of `QuadraticDivMod.system`, preserving its empty register block and
literal sum-of-squares expression. With visible coordinates `q,r,n,d`
and one auxiliary coordinate `s`, its natural-part equalities are

```
n = q*d+r,     d = r+s+1.
```

The stored integer polynomial has degree at most four. Some internal `s`
makes it zero exactly when `d>0` and `divmod(n,d)=(q,r)`. In particular,
zero denominators admit no certificate; no positive-denominator side
hypothesis is supplied to this equivalence.

The dedicated Lean checks include the actual ZFC totality derivation,
literal expression degree, universal internal semantics and dependency
audits. This is a prerequisite for internal arithmetic trace interpretation,
not a completed internal primitive-recursive compiler or consistency
biconditional. Those obligations remain open.
