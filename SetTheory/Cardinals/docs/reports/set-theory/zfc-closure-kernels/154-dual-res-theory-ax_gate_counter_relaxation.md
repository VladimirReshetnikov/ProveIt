# A sufficient whole-AX relaxation for residual counter values

This is a command-level search contract, not a certificate for a modified
comparator or transition table.

Suppose a revised complete AX capture gate has exactly the old result in
the current theorem, theorem stack, cache, selector, scratches, next-proof
counter, and proof-list registers. In particular, it clears the current
formula exactly when `c=a` or `c=b`; otherwise it preserves the correctly
constructed native bundle. Allow the additive parameter counter D to
return an arbitrary natural value instead of zero, subject only to

```
D=0 on every gate input with c=0.
```

The exact value when `c>0` may be arbitrary. This still gives a sound and
complete proof enumerator with the unchanged formula calculus.

Soundness is immediate from the old theorem-field invariant: D is merely
an arbitrary nonnegative additive parameter. Changing it cannot make a
later AX or GEN instance unsound, and MP continues to check its literal
implication code.

For completeness, begin each intended proof with the old START command
`CAX(0,1,1,0)`. Its private code is zero, so it still clears D and the
cache from every retained state. Each intended axiom, bundle, or GEN
block subsequently starts with D=H=0. Its usual NIP/DROP cleanup can
first isolate its desired result X without changing the residual D and
with H=0. Then append the universal cleanup

```
CAX(0,0,0,0); NIP^10; DROP; NIP.
```

The new AX output label b and private code c are both zero, regardless
of the unknown current D. Thus its gate is disabled and the c=0
hypothesis makes D zero. The ten popped entries
end with the old current X; the other nine are logical or GEN entries,
which cannot equal the membership contradiction 1. DROP and the final
NIP restore `(X,w,0,0)`, unless X is already a contradiction and the
machine halts. Thus the standard proof-block contract is restored.
Replace any ordinary or copy-return MP reset suffix by the same universal
cleanup. The no-push move and cache variants already have their shorter
proved return blocks. The candidate numbering and reach argument are
unchanged. No dependence restriction on the residual D is required;
it may even depend on the caller's retained state, since the cleanup
works uniformly for every natural residual.

The earlier proposed restriction allowing residue only when a<c is a
sufficient special case. Completely arbitrary output D even at c=0 is
**not** licensed by this argument: START would no longer necessarily
reset an unknown retained counter.

This freedom applies to the complete gate result. It does not justify
altering D between the first and second comparisons. Such an intermediate
change can corrupt the second freshness test; the previously identified
case `a=c=2,b=0` is an explicit danger. A concrete implementation must be
proved to satisfy the whole-gate contract before this abstract result is
used.
