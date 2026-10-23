# Checked free-carrier numerical tail

[`FreeCarrierRatio.lean`](Lean/DiophantineConsistency/FreeCarrierRatio.lean)
proves the arithmetic tail of the package-59 free-carrier equation, with all
source parameters left generic. It assumes only the stated primitive numerical
bounds and the explicit scale identity `cap=32*t`. For a source instance,
`t` will be `b*B^W`; this module assigns no source meaning to it.

`FreeVars` contains natural `h,s,w,C,i,j`. The first five are positive in the
numerical theorems. Its absorbed CRT index `j` may be zero; the proposal's
strictly positive input for that coordinate is `j+1`. The final witness `n`
in `finalValue` is strictly positive in the existence theorem. All integer
registers and `finalValue` are executable data.

The integer `base` uses `phi=C-(2R+1)-b*w`, which can be negative before a
zero is decoded. The theorem `base_C` proves its actual carrier is exactly
the supplied free positive `C`. Primitive register bounds and both strict
Pell majorants hold already at `C=1`, including assignments with negative
`Q`. The normalized margin is the literal polynomial

```
m=K^2*(4*t-g)-16*t*(C-K*Y)^2.
```

`margin_scale` proves `8*m=oldMargin` from `cap=32*t`.
`carrier_range_of_margin_pos` reconstructs `C>2R+1+b*w`. Only after this
step does `toRatio` convert the integer offset to its natural value.
Its checked base, H, I, and margin equalities preserve the actual registers.
The reverse `ofRatio` retains the old positive carrier, with no restriction
on the nonnegative absorbed index.

The final norm uses `J*(n+(b*w)^2)+Q`. To reuse the checked generic finalizer,
write `n=nu+1` and set `Qstar=J*((b*w)^2+1)+Q`. `shifted_Q_bounds` proves
`0<Qstar<V1` from the actual registers; `Qstar_dvd_iff` preserves `J|Q`.
Thus `exists_finalValue_zero_iff_conditions` proves that a positive final
witness exists precisely when both original radicands are squares, `J|Q`,
and `m>0`. The margin is recovered before separation and integrality of the
radicands are used.

`ratio_sound` then gives the existing Jones conclusions: `b` is a power of
two, `N^2` divides `choose(2R,R)`, and `8*g<cap`. `ratio_complete` constructs
the free-carrier witnesses and a strictly positive final coordinate from
those first two conditions and the original stronger bound `32*g<cap`.
It reuses the checked `NativeNineRatio52` theorem after exact carrier
transport. No source, coefficient calibration, machine, or consistency
hypothesis is discharged by this file, and it makes no 473-operation claim.

The regression file checks `C=1` with `Q=-18`, positive shifted numerator,
exclusion of every positive final witness at that negative margin, and the
old `phi=j=0` boundary. All audited proofs use only the standard Lean axioms.
