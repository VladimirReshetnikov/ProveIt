# Independent conditional parent-transport audit

The read-only [audit](audit.py) of `66a62a1596` exited 0 in session 78105.
Its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
bind the result. It checked the committed packet and paired source/object
hashes, both recorded compiler and direct-import exits, each direct parent
object against its matched 70-source state, and author outer session 61493
exit 0. The parent comparator was rerun and exited 0. Both outputs match and
their single axiom reports contain Lean metatheory `propext`,
`Classical.choice`, and `Quot.sound`, with no warnings, errors or `sorryAx`.
The audit did not run Lean; package-transitive/dynamic ancestry and the
Foundation wrapper's unobserved outer exit remain inherited.

The exact model theorem assumes naturals b,q,K,w,F,alpha,C,z in an IΣ₁ model,
q=b+1, z>0, C>0, F+alpha+C=q, F<q, q≤w, and

```
(K+w)q+q = (K+w)(F+alpha)+F+z(q−1)+1.
```

It constructs G=b(z−1)>0 with b∣G and (K+w)C=F+G. No b>0 assumption is
needed: under the other hypotheses it follows from the equation and
inequalities. The audit checked 375 bounded standard-integer instances as a
sanity check; this finite survey is not the model proof.

The author reports an initial root-directory failure, a later unfinished
proof with `sorryAx`, a successful intermediate version with an unused
premise warning, and a successful clean exploratory version; separate full
transcripts are not retained in this packet. The pinned successful paired
compiler output is checked independently above.

This conditional statement does not derive its premises from a positive
carrier zero, identify the literal graph's C and G, prove the rank phase or
all-model converse, calibrate either fixed tuple, or produce an iPRA proof.
