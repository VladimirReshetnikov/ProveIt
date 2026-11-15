# Independent review of the AX11QGH command proof

Reviewed inputs: `construction/AX11QGH/proof.tex` and its command checker,
with the corresponding exact table SHA256
`513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1`.
The parent development's source and literal verification receipts are separate
from this manual mathematical inspection.

No off-by-one, fourth-operand, or saved-binder error was found. The principal
identities were recomputed as follows, writing the eleven pushed entries as
`q0,...,q9,t` and remembering that Shift checks the cache before moving it.

| Word / clause | Independent check |
|---|---|
| AX fourth field | After the extra push, the full MP parameter reader receives `t=d=h=0`. Its comparison against `I(0,z)` returns zero in both `z=0` and `z>0` branches, preserves the stack, and leaves offset `z`. |
| AX followed by 10 Shifts | Returns top `q8`, cache `q9`, and stack `[t;w]`. |
| AX followed by 11 Shifts | Returns top `q9`, cache saved `t`, and the original underlying stack. None of these eleven Shifts tests the saved top. |
| Pop = AX0 followed by 12 Shifts | The twelfth Shift tests saved `t`. If it is not one, the effect is precisely to expose the old stack head in the cache while preserving `t` as visible top. |
| Selector j | After `j+2` Shifts the visible top is `qj`, the cache is `q(j+1)`, and the stack begins with `q(j+2)`. The following `9-j` Pops remove exactly the remaining generated entries plus the reserved saved zero. |
| Restricted rho | Offset-setting MP supplies `u`; the AX field `D truncated-minus u` reconstructs `D` because `u<=D`. The selected instance retains the old offset as its fourth logical parameter. |
| New generalizer | Push and Shift leave `(0,w,0,a)`. AX with binder `i` consumes that cache into `U(i,a)` before any Shift can test it. Eleven Shifts return `(U(i,a),w,0,0)`. This remains correct for `a=1`, `i=0`, and numerical zero aliases. |
| MP suffix | On `[a,I(a,b),0;w]`, the second Shift detects `a=1`; otherwise MP derives visible `b`. The final Pop detects `b=1` or removes exactly the reserved zero. Without that zero the original underlying stack would be consumed. |

The generalizer's binder is the explicit AX parameter `c`; its body is the
incoming `h`, not `h+y`. The unchanged Q-oriented axiom family is therefore
preserved, while the generalization compiler loses the former offset-setting
command. This is a command-interface change, not a new axiom or an unproved
logical equivalence.

The all-store compiler's primitive-recursive majorant argument also carries
through: with compiled-word length bound `L`, command bound `K`, and
`B(j)=Phi_K^(L*(N-1-j))(s0)`, every premise call at an earlier line `i<j`
falls below `B(i)`. The induction assertion is a finite Boolean conjunction
over bounded store codes. The proof does not invoke induction on an unbounded
universal-store assertion. The four-field word encoding and cofinal prefix
consume the genuine fourth field; the candidate `(Ne+2)^2` time bound safely
covers the sum of earlier draining lengths. The counter increments at fresh
selection and the carried store is never reset.

The numerical-calculus calibration is inherited from the explicitly identified
latest incoming AX11H/QAX11H written proof, whose independent inspection is
described in `AX11H_AUDIT.md`. This review is a written mathematical audit;
it does not claim a new end-to-end Lean verification.

Both AX11QGH and the separate physical-register-placement candidate AX11HR
passed exact graph-novelty comparison against the complete recognized literal
194-state frontier, including broader cosmetic transformations. The two
canonical tuples also differ from each other. The portable checker and its
fresh receipts accompany this note.
