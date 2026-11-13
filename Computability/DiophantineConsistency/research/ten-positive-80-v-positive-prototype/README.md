# Positive signed V for the 80-operation graph

`TenPositive80VPositive.graph_v_positive` proves that the signed integer
intermediate V of the actual 80-operation graph is strictly positive in the
model difference ring. Its hypotheses are a model of IΣ₁, positive inputs,
a zero of the graph output, positive β, and the explicit low/high port
inequalities. It does not assume odd β or V positivity.

The proof first obtains the graph's natural rank and its window, and the
independently proved graph size inequality `2*q^4 < c`, hence `rank < c`.
Since the graph's T input is positive, its signed trace `c*T-rank` is at
least one. The graph factor definitions give `c+1 < F²`, where F is the
strong Pell factor. The exact graph identity `V = F²*(c*T-rank)-c` then
gives V > 0. This is a model-theoretic necessary condition on an actual
positive graph zero; it does not establish a phase, machine halt, converse,
or an internal iPRA proof.

`observations/attempt01/` retains the failed check (two elementary tactic
issues). `observations/attempt02/` records the successful guarded check of the
current source. The resulting object is
`/tmp/tenpositive-80v-positive-40dozh92/Direct80VPositive.olean`, SHA-256
`fb2f5a54c21ce7e0b6420d65c224298289004b20af1733471cbd2b525973c188`.
The receipt records source/runner/tool pins, selected prototype object pins,
resource samples and output. The check inherits the existing project and
package providers; it does not independently rebuild their complete transitive
source-to-object ancestry or audit dynamic libraries. The local object in
`/tmp` is an exploratory result, not a reproducible complete provider bundle.
