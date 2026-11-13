# Scaled digit bounds and local carry arithmetic

This packet checks six elementary results in every model of IΣ₁. For a model
radix width `w`, if every digit of `X` below `k` is at most `D`, its remainder
modulo `2^(w*k)` is at most `D * rep(w,k)`. The induction predicate is Σ₁
provided by the source's `definability` proof. The bound holds for arbitrary
model `D` and therefore can accommodate the compact44 exceptional digit bound
3, provided the required digit hypotheses are established separately.

For an externally finite index type, the packet derives weighted prefix and
single-column bounds using `D` times the coefficient mass. It also checks the
scaled repunit mass inequality used by the existing end-around carry proof,
under its explicit mass hypothesis. Two local lemmas show that an outgoing
quotient carry vanishes if `raw + carryBound < radix` and the incoming carry is
bounded, and that a column identity reduces to `digit = raw` when both carries
are zero. These estimates do **not** construct a global cyclic carry, prove its
bound, prove a clean predecessor, or establish the actual MC digits. A
hypothetical clean predecessor cannot be inferred from Boolean assumptions at
all positions: digit 1063 may be 0 through 3, and temporal rotations may combine
adjacent source digits.

The paired replay imports the independently audited author and peer 24-module
window providers. It checks the direct Lean imports, source pins, matching object
hashes, six axiom reports, and reruns the parent audit before and after. The
parent audit has no complete axiom inventory and does not authenticate all
package-transitive or dynamic ancestry. The resource monitor samples usage and
is not a hard whole-process-tree quota. The claim is model-level arithmetic,
not a compact44 graph, machine simulation, checker, or internal PRA proof.

The exploratory attempt 1 exited 1 (session 78929): the then-selected import
lacked finite-sum lemmas, and `add_le_add_left` had the wrong operand order. Its
source and full log are retained in `observations`; printed axiom lists for the
failed declarations contain `sorryAx` and are not evidence. The corrected
exploratory session 64517 exited 0 without warnings; its log is retained.
