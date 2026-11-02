# Independent review of the model strong Pell seed

The read-only audit of commit `e30959deed` exited 0 and checks the recorded
paired bounded replay against the independently audited 70-source parent.
The author's tool session 50440 records outer exit 0; each of the four Lean
child compilations and four direct-dependency checks records exit 0. On each
side the suffix first compiles the pinned `ArithmeticPellPigeonhole` source,
then compiles `ModelBSeed` against that freshly built object. The audit
rehashes both source and object chains, checks all 64 project-parent symlinks
per side and the BusyBeaver link, and verifies the recorded direct imports.
The corresponding objects match across siblings.

The theorem's exact assumptions are an `IΣ₁` model, natural model elements
`a,b,c`, and `b>0`, `c>0`. It produces positive `t,f,i` with

```
f = xcoord t a,
ycoord t a = b*i*c*c,
f*f = 1 + delta a * (b*i*c*c) * (b*i*c*c).
```

The model pigeonhole theorem supplies a positive index whose ordinate is
divisible by the actual modulus `b*c*c`; positivity of the ordinate gives
`i>0`, and the Pell norm gives the last equation. The result makes no
assumption about a fixed port or a rank phase. Positivity of `b` and `c` is
material: at a positive index the ordinate is positive, so either zero
factor would make the displayed ordinate equation impossible. A supplementary
check of 80 ordinary examples, including `a=0`, verifies the recurrence,
divisibility and norm in a finite range; it is not a proof of the arbitrary
model theorem.

Each pigeonhole compilation reports exactly three deprecation warnings: two
for `push_neg` and one for `mul_le_mul_left'`. The seed compilation reports
no warnings and its one axiom report is `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx`. These are Lean metatheory dependencies, not
axioms asserted for object-level iPRA. The author documents earlier failed
path and proof attempts separately; those attempts are not the paired result.

This is a model-level seed, **not** the 69-operation thirteen-variable
converse, a fixed-port checker calibration, or an iPRA derivation. It does
not construct the private auxiliary seed, rank phase, signed ordinate, or
carrier quotients. Both sibling builds reuse the same historical Foundation
package provider and compiler. Package-transitive and dynamic ancestry remain
inherited, and the Foundation provider's original outer wrapper exit remains
unobserved. The audit rehashes the recorded outputs and observations but does
not independently rerun Lean or witness the original processes.

`CHECK.json` records the hashes and finite checks, and
`terminal-observation.json` binds the audit's actual exit 0 to that receipt.
Run while the historical temporary outputs remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/thirteen-model-strong-seed-independent-audit/audit.py
```
