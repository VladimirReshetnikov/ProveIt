# Independent reduced-denominator induction audit

The read-only [audit](audit.py) of `dd11641315` exited 0 in session 2406;
its [receipt](CHECK.json) is bound by the
[terminal observation](terminal-observation.json). It checked committed
sources and evidence, both seed and output objects, 67 project links and
BusyBeaver links per side, direct imports, compiler logs, recorded child
exits and author outer session 54640 exit 0. The immediate simultaneous-state
independent parent audit was rerun and exited 0. That chain retains the
separately documented older square-divisor audit's README-drift guard failure.
The two logs each contain three axiom reports using only Lean metatheory
`propext`, `Classical.choice`, and `Quot.sound`, with no warning, error or
`sorryAx`. The audit did not rerun Lean. Foundation's unobserved
outer-wrapper exit and package-transitive/dynamic provenance are inherited;
the recorded RSS values are sampled leader peaks, not whole-process quotas.

The final theorem is quantified over an `IΣ₁` model and assumes model
naturals r>0, b>0, `Bez a b 1`, and (r+1)(vb)²=ra²+b². It concludes b=1,
with no v>1 premise and no graph or strong-norm assumption. The source
defines the exact predicate P(k): there exists x with `Bez x b 1` and
(r+1)(kb)²=rx²+b²; it invokes Lean's `definability` to obtain its Σ₁
classification, then `InductionOnHierarchy.least_number` in the model.
The proof excludes k=0 by b²>0, handles k=1 by square and Bézout
cancellation, and uses the previously checked simultaneous smaller-state
theorem in the remaining case. Thus this is model-level least-number
reasoning, not external well-foundedness of a nonstandard model.

The recorded failed preliminary session 6714 exited 1 with an incomplete
report containing `sorryAx`; its source and summary are retained and are not
evidence for the final theorem. Still missing are normalization from the
actual arbitrary signed numerator and nonzero denominator to this reduced
natural state, binding the graph's cleared norm, recovery of the strong norm,
and a proof-producing bridge or derivation in object-theory iPRA.
