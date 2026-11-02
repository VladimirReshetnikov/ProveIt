# Independent audit of the model auxiliary Pell seed

The read-only audit of commit `d636a93093` exited 0 in tool session 53000.
It verifies the recorded paired suffix replay and reruns the independently
audited strong-seed parent check without invoking Lean. The original wrapper
session 70281 records exit 0; both sides record three compiler exits and three
direct-dependency-check exits of 0. Corresponding source and object hashes
match. The audit checks all 66 parent project links per side, both BusyBeaver
links, the pinned compiler and source inputs, and the exact direct dependency
chain from `ArithmeticPellSquaredSeed` through
`ArithmeticPellAuxiliarySeed` to `ModelBAuxiliary`.

The model theorem assumes an `IΣ₁` arithmetic model, natural `a,R,b`,
`b>0`, and `R % 4 = 3`. With `c=ycoord R a`, it produces positive
`f,i,T,u,y` satisfying the strong norm for ordinate `b*i*c*c`, two
congruences, the displayed positive quotient and absolute-difference
equations, and the auxiliary norm. The phase condition gives `R>0` and
therefore `c>0`; the strong-seed theorem supplies the extra multiplier.
The precise definitions and equations are in the source packet. Six finite
ordinary examples with `R=3`, `a=0,1,2` and `b=1,2` independently satisfy
the displayed equations; these are sanity checks, not an arbitrary-model
proof.

The two intermediate suffix compilations recorded no diagnostics. Each
final theorem report lists `[propext, Classical.choice, Quot.sound]`, with
no warning or `sorryAx`; these are Lean metatheory dependencies, not axioms
asserted for object-level iPRA. The original exploratory shell chain recorded
an overall exit 0, but its individual child exits were not separately
observed; the later paired receipt does record the six child exits. This
audit rehashes those recorded artifacts and observations rather than
independently rerunning Lean.

The theorem does not construct the signed carrier coordinate or its sign
congruence, prove the 69-operation converse, calibrate the fixed ports to
the checker, or establish an iPRA derivation. The paired suffixes reuse the
same historical Foundation/package provider and compiler; package-transitive
and dynamic ancestry remain inherited, and the original Foundation wrapper's
outer exit was not captured. The 70-source parent is a pinned closure rather
than a build of later unrelated source additions.

`CHECK.json` records all object hashes, link counts and finite examples;
`terminal-observation.json` binds the actual audit exit to its receipt. Run
while the original temporary paired outputs remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/thirteen-model-auxiliary-seed-independent-audit/audit.py
```
