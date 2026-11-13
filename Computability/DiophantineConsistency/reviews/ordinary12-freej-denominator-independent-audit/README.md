# Independent bounded replay of the free-J denominator sign

The independent bounded replay of the source in commit `62a8e07a9b` exited 0
in tool session 55667, with receipt SHA-256
`f0422f93287536aecccea34c298741cc96644551d3357400d31863ab1d31e1f4`.
Its fresh output object and seven axiom reports match the two recorded prior
runs. The separate read-only audit also exited 0; it rehashes all three source
copies, objects, V-bound seed copies and the 83 recorded earlier parent
inputs. The audit receipt and the fresh compilation receipt are retained here.

All three compilations use **the same historical V-bound seed and underlying
provider**. They are repeat compilations, not two independently rebuilt
source-current parent providers. The source packet reports that the first
original wrapper exit was observed as 0, while the second original wrapper
printed PASS but its outer exit was **not separately observed**. The fresh
independent wrapper's actual exit 0 does not retroactively supply that missing
observation. The compiler and dependency-check exits recorded inside each
receipt are 0; all seven reports name only `propext`, `Classical.choice` and
`Quot.sound`, and no warning or `sorryAx` was recorded.

Under the model-level assumptions of the preceding V-bound theorem—positive
coordinates, an internal zero of the free-J literal and the stated port
inequalities—the new theorem proves strict negativity of the signed-pair
evaluation of the **proof expression**
`D=c⁴·2(1−Q)(n+V)`. It is not a literal graph gate. The proof obtains `Q>1`,
`V>c>1` and `n+V>0`, then combines the signs. The audit also checks a finite
family of these inequalities and the generic `Q=1`, `n+V=0`, and `c=0` zero
edges; those controls do not claim to be full-graph valuations.

The source identifies the proof-only `c`, `Q` and `V` expressions by
inspection and the previously compiled graph shape. The signed-pair bridge
that substitutes the denominator into the cleared auxiliary norm remains
open. The polarized literal uses the opposite sign in its intermediate
`A`, so the ring polarization identity and its signed model substitution
must still be connected explicitly. Reduced-denominator descent, fixed-port
calibration and an internal iPRA derivation are also unproved here. The
historical provider's transitive and dynamic ancestry remains inherited.

`terminal-observation.json` records both independently observed exits and
binds them to their receipts. Run the read-only audit from the repository
root while the original and fresh temporary outputs remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-freej-denominator-independent-audit/audit.py
```
