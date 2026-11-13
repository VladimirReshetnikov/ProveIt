# Free-J q binding and conditional cancellations

For a nonnegative integer β in the actual free-J graph's first port, Lean
proves its signed q pair is exactly the natural pair representing
`1 + J·β` and is positive. Here `J` is the graph's first variable. No rank,
positivity of the other variables, or checker premise is used.

The graph-specific cancellation theorem then assumes explicitly that the
model interpretation of β equals `2^590069−1`, together with `q³ ∣ Y`,
`q⁵ ∣ (3+4Y(X+1))t`, and `q ∣ 3·2ᴿ`. It concludes `q⁴ ∣ t` and `q ∣ 2ᴿ`.
`Y, X, t, R` remain separately quantified; the graph, rank, and norm
bridges needed to establish those divisibilities are not supplied here.
The two conclusions come from independent branches, so the later power
premise is not used to establish the early q⁴ cancellation. The stated
model port equality is a hypothesis, not compact44 checker calibration.

Fresh bounded replay session 75131 exited 0 and printed
`PASS_BOUNDED_FREEJ_Q_GRAPH_BINDING
17dd9ce902ae31b9756246c3754408c98a4ee4c8e240d5d31b432b4f6b137866`.
The receipt records five axiom reports, source/object hashes, direct imports,
recompiled historical rank adapter, and inherited provider and source
closure checks. Exploratory session 47460 also exited 0; earlier attempts
failed from a missing Lean root option and missing namespace import. This is
single-author historical model evidence, not a full paired replay, a dynamic
package audit, or a proof of an iPRA derivation.
