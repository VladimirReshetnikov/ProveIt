# Positive ordinary-tail coordinates from the auxiliary Pell seed

`CompactAuxPositiveCoordinates.auxiliary_f_pos` proves in any `IΣ₁` model
that, when `R>0`, `c=ycoord R a` and `f=xcoord (R*c) a`, one has `c>0`,
`f>1`, `f-1>0`, and `(f-1)+1=f`. It uses the model-level bounds of the
Pell recurrence, including for nonstandard indices. Thus `t=f-1` is a
strictly positive model natural for the ordinary-tail coordinate.

`ordinary_coordinates` additionally takes `i,w>0` and the normalized
auxiliary relation `f*f=1+delta a*(i*c*c)*(i*c*c)`, and proves

```
0 < f-1,  (f-1)+1=f,
0 < delta a*i,  0 < delta a*i+w,
delta a*(f*f-1) = (c*c*c*c)*(delta a*i)*(delta a*i).
```

The `f-1` positivity and square identity are useful for the ordinary-tail
construction. The separately proved positivity of `delta a*i+w` does **not**
supply its graph coordinate: the exact ordinary-tail bridge instead requires
`n=delta a*i+(y-w)` (with this seed's `w` identified with graph `V`). The
separate [ordinate-order theorem](../compact44-aux-ordinate-order-prototype/README.md)
provides the needed `w ≤ y` under explicit seed hypotheses. The positivity
and square facts apply to the corresponding variables in
`CompactOuterPellSeed.seeds` once its rank positivity is supplied. This
client does not establish that any graph evaluation equals these expressions,
construct the other positive coordinates, prove the free-J literal zero,
identify retained/displayed coefficients, or establish an iPRA derivation.

The bounded single-author attempt `observations/attempt01` actually exited 0
without warnings or `sorryAx`. Both named axiom reports are exactly
`[propext, Classical.choice, Quot.sound]`, which are Lean metatheory
assumptions rather than axioms added to the object theory. Source SHA-256:
`fbe1ce87f2ea8dbbd6857d450fb4f4bc74b01a5de4c419528e997de1ea9d42a8`;
object SHA-256:
`935500d93043c89020ee84d229889773bb041117e329ba921fc4adb52a5d263a`.
The compiler receipt, exact source, direct import/companion guards and
selected provider inventories are retained under that attempt. The selected
seed and halt overlays had 531 equal overlapping project names at preflight;
the recorded direct guards and selected inventories were unchanged at the
final checks.

This is a single mixed-provider exploratory build. Point-in-time overlap and
guard checks do not authenticate the entire transitive, package or dynamic
ancestry or imply a matched paired replay. Filesystem and resource checks do
not establish continuous monitoring.
