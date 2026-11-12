# Independent source review: eta-natural factor units

This review pins the corrected source in
`research/ordinary13-eta-natural-unit-norm-bridge-draft/`. The author's
literal generator and checker reproduce. The independent checker compares
all 85 prototype rows, 13 input bindings, four port bindings and all 21
field mappings to the generated Lean source; it exhaustively checks all
1,024 first-factor residues and all main/auxiliary/strong residue patterns
(256, 256 and 64 cases). Run `python3 -I -S -B check.py | cmp - receipt.json`
from this directory. These checks do not elaborate Lean or authenticate any
model provider.

For the new first exclusion, write `b,z,x,s,k` for the five residues,
`q=1+b`, `Y=q³s` and `ell=xY²k`. If b is even, `b²=0 mod 4`, so the
factor `1+z²−b²(1+ell(ell+k))` is `1` or `2 mod 4`. If b is odd, q is
even and Y is divisible by four, so ell vanishes mod 4 and the factor is
`z²`, namely `0` or `1 mod 4`. Thus the factor is never the residue of −1.
No positivity is used, and b may be any residue of an arbitrary signed port
expression. This proof is specific to the first factor's *shorter* `b` scale;
`FreeJ13.first_ne` uses a different q³-scaled factor and is not substituted.

The main, auxiliary and strong expressions match the argument order of the
selected generic `FreeJ13.main_ne`, `aux_ne`, and `strong_ne` sources. In
particular, their shared `delta` is `(3+4a)+a*a`, the auxiliary and strong
use the unshifted input `.var 3`, and the main norm uses the generated actual
`Dstar`. These are syntactic source checks; the claimed `rfl` proofs and
imports are unelaborated. The source correctly uses the forward implication
from a negative signed pair to residue −1 to exclude the negative unit; it
does not infer a converse.

The output's parenthesized factor order is `((F0*F1)*Fa)*Fs−1`. The source
uses the same first/main/aux/strong order in `product5`, with a fifth +1
factor, then takes magnitude one for each factor and applies the individual
negative-unit exclusions. The later `unit_iff_one` conversion yields the
four signed ring residual equations; it does not create natural roots, prove
positive inputs, represent ports, or establish an equation bridge.

An earlier version of this draft stated `first_bad` with
`1+(z*z−b*b*(...))` but supplied the normalized expression
`(1+z²)−b²*(...)`. Those expressions agree in a ring but are not the same
syntactic term for a direct `exact` application. The author revised
`first_bad` to use the latter expression, matching the `he` result including
the let-bound `Y` and `ell`. This review pins the revised bridge SHA
`7bf4388808c8e463461f51972bbbbb4b93a5092f80fb7ac10b86ab49e7601851`;
the repair and the remaining `decide`, simplifier, `ring` and signed-pair
steps have not been checked by Lean.

No further mathematical mismatch was found in the inspected factor patterns.
The prototype is a structural experiment. Graph-to-model natural/rank/port
bindings, the separate factor-to-natural-norm adapter, all-model zero maps,
fixed byte/PDF semantics, provider compatibility and an internal-iPRA endpoint
remain separate obligations.
