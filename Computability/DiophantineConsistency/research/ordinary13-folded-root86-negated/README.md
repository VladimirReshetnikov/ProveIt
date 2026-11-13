# Sign-reversed 86-operation first-root fold

This is a source-only candidate submitted for independent review, not a new
Lean theorem or replacement endpoint. It has 13 positive inputs, 86 live
binary gates and exact specialized total degree 26 at the authenticated
compact44 ports. It is obtained from the independently reviewed 88/30 free-J
graph by replacing the first-root coordinate using

```
sigma = k*Bt − r_old,       r_old = k*Bt − sigma.
```

The graph's input slot is still named `r` in `candidate.json`, but represents
sigma. The substitution is an involution over every integer valuation, and
the output agrees exactly with the 88 graph under it. The 86 graph is the
previous folded-root probe with its `g31 = (ell+k)+r` changed to
`g31 = (ell+k)−sigma`. It retains all thirteen inputs and the four ports.
The original plus-sign probe is unchanged.

## One existence direction from canonical halt data

At the compact44 tuple, assuming the existing standard-natural parent
zero-to-halt calibration and the previously reviewed source/port binding, a
positive 88 zero gives a halt. The existing halt-to-witness construction then
produces a positive 88 zero with `r_old−k*Bt<0`, by the independent canonical
sign argument `../ordinary13-folded-root86-canonical-sign/`. Thus
`sigma=k*Bt−r_old>0`, and the exact substitution gives a positive 86 zero.

This invokes the inherited calibration and construction, including their
external fixed-byte association; this packet neither replays their full source
ancestry nor compiles a new Lean theorem. It does not assert the halt premise
itself. The direction is an **existence** result in standard naturals under
those cited existing interfaces, not a pointwise positive map for every 88
zero.

## Reverse guard fails for a full toy-port zero

A positive candidate tuple maps back directly only if `k*Bt>sigma`; exact
zero equality alone does not guarantee positivity of `r_old`. The previously
reviewed full 88 toy-port zero in
`../ordinary13-folded-root86-toy-full-zero/` gives a full candidate zero
violating that guard. Retain its positive inputs other than the first-root
slot and its notation `(ell,k,s,t,tau)`; in particular `s>t`, `tau>ell=m*k`
and `Bt>0`. The sign-reversed first residual is zero for either

```
sigma_plus  = ell+k+s−t−tau,
sigma_minus = ell+k+s−t+tau.
```

The toy review proves sigma_plus>0. The second choice is also positive, and
in fact exceeds `k*Bt`: at its fixed toy ports, `q=32`, `K0=9`, `C=17`,
`F=1`, `X=q*w` imply `Bt=17*X+4864<18*X`, while `Y>=256` gives
`m=X*Y²>Bt`. Therefore `sigma_minus>tau>m*k>k*Bt`.
Changing only sigma changes the sign of the first root Z and leaves the other
three residuals unchanged, so this is a **full positive toy-port 86 zero**
whose direct reverse image has negative first coordinate.

This does not disprove unrestricted existence equivalence: the other root
sigma_plus in this same toy example maps to the reviewed positive 88 witness.
It also does not settle whether every positive candidate zero at compact44 can
be repaired using another root or changing other coordinates. The missing
candidate-zero-to-parent-zero existence direction is open.

## Size and validation

For the sign-reversed graph write

```
delta0=M*(k−sigma)+Y*qm−q³*Bt,  Z=M*ell+delta0.
```

The exact expansion
`A0=2*M*ell*delta0+delta0²−M²*(1+ell*k)` bounds `deg(A0)<=13`.
The main residual has the same cancellation as the previous probe, and the
other residual degrees are at most 13 and 10, so the output degree is at
most 26. A whole-graph ray over the four authenticated compact44 byte values
modulo 1,000,000,007 has degree 26 and leading coefficient **316822945**;
this proves the specialized integer polynomial has exact degree 26 externally.

The checker pins the parent and earlier probe, checks the precise one-row
change and 86-gate liveness, validates the cancellations in a sparse integer
polynomial ring, tests signed substitutions, authenticates P72/P115 ports,
and computes the whole-graph modular ray. Its finite checks do not replace
the symbolic zero and existence arguments. No Lean, PDF or file-semantics
theorem or global minimum is claimed.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-negated-independent/`.
