# Independent review of the paired model square-divisor suffix

The read-only audit of commit `bd56831045` exited 0 and checked the suffix
against the independently audited 70-source parent. Both recorded suffix
compilations exited 0, used matching source bytes, and produced identical
object SHA-256
`5c745c178aa64429340e217eb0ef3e2bffba98e747f7c0a29ff3c1ca25c95f97`.
Their recorded direct project inputs are the corresponding matching fresh
`ArithmeticGcdNormalization.olean` objects from the two parent siblings.
The three recorded axiom reports match and contain only `propext`,
`Classical.choice` and `Quot.sound`; there are no reported warnings or
`sorryAx`. The author wrapper's recorded tool session 18427 exited 0. The
earlier comment-only source revision is correctly identified as a separate
historical replay.

The main theorem is a **model-level implication**: in the stated `IΣ₁`
model, if a four-natural Bézout certificate for `a,b` and the reduced norm
`t*b²=r*a²+b²` are supplied, then some natural model element `s` satisfies
`r=b²*s`. Neither positivity nor `b!=0` is assumed. The explicit squared
certificate gives Bézout for `a,b²`; the norm supplies `b² | r*a²`, and
two applications of the parent cancellation lemma give `b² | r`. With
`b=0`, the certificate and norm force `r=0`; the source proves that edge as
a corollary. This does not construct the original gcd or reduced norm.

As a supplementary finite check, the audit enumerates `0<=a,b,r,t<=12`
under the natural coprimality and reduced-norm conditions and validates the
displayed four-natural squared certificate and divisibility. The 137 states
include `a=0`, `b=0`, `r=0` and `b>1` cases. This check is not a proof of
the unbounded theorem.

The audit rehashes the exact suffix packet and existing temporary objects,
the direct parent objects, the original receipt and the independently audited
parent receipt. It does not rerun Lean or independently witness the earlier
compiler processes. Both suffix runs reuse their respective 70-source parent
outputs and the same Foundation/package provider; transitive and dynamic
ancestry and the Foundation wrapper's unobserved outer exit remain outside
the evidence. This does not establish termination of the integrality descent,
the signed graph application, fixed-port checker calibration or an internal
iPRA proof.

`CHECK.json` records the source, parent receipt and object hashes and finite
edge counts. `terminal-observation.json` binds the actual audit exit 0 to that
receipt. Reproduce while the historical temporary outputs exist:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-model-square-divisor-independent-audit/audit.py
```
