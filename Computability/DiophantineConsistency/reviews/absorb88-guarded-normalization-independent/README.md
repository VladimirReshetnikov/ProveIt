# Independent source review of the guarded 88→89 bridge

The [guarded bridge](../../research/ordinary12-absorb88-guarded-normalization-draft/Absorb88GuardedNormalization.lean)
and its [ring identities](../../research/ordinary12-absorb88-guarded-normalization-draft/Absorb88NormalizationRing.lean)
have the stated source-level implication: under the displayed guard, a
positive 88 zero yields a positive 89 zero at the same ports. This review
did not rerun Lean or independently authenticate inherited providers.

For the original natural-model tuple put `b=J*beta`, `q=1+b`, `A=K0+w`,
`D=q(qA+1)`, `Bp=qA`, and `Bn=(F+alpha)A+F`. The source requires natural
model witnesses `j,u,Fnew,anew,t` satisfying

```
F=Fnew+b*j,  alpha=anew+b²*j,  D*j=u+t,
Fnew>0,       anew>0,            t>0,
q*(Bn−Bp)=b*u                 in the difference ring.
```

These are genuine additional hypotheses. Since `u` may be zero, the guard
can include a zero original transport as well as a strictly negative one;
it does not show that an arbitrary 88 zero supplies such witnesses.

The ring normalization replaces only coordinates 1, 2, and 7. Its first
two updates preserve the signed rank component
`G=alpha+b(q−F)`. Writing the original scaled transport as
`Bt=q*((q−F−alpha)*A−F)`, the final guard equality gives `Bt=−b*u`,
and the updated transport is `b*(D*j−u)=b*t>0`. The new coordinate 7 is
`first+(1+k*b)*t`, where `first` is a positive first Pell root extracted
from the original zero. The explicit positivity assumptions ensure the
replacement is a positive natural tuple; these are not consequences of
the ring identities alone.

The ring lemmas preserve the actual main and ordinary residuals. Their
first-residual identities give first-part value `b*first` and matching
square from the first Pell norm, so the updated first residual vanishes.
The model proof obtains the original residual zeros from the actual 88
zero, constructs the positive updated 88 zero, and derives the strict
positive-transport inequality needed by `Absorb88Conditional`.
That imported theorem supplies an existential 89 witness at the **same
ports**; the final 89 witness need not be the intermediate updated 88
tuple. This review does not independently reprove the imported conditional
theorem or establish guard existence, unrestricted 88→89 equivalence,
or an iPRA endpoint.

The two source hashes, output object, and four direct ring/model input
object hashes match the packet's recorded values on the stated search
path. The following read-only check exited 0 and produced
[`result.json`](result.json):

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/absorb88-guarded-normalization-independent/review.py
```

The model packet reports a successful Lean check with
`[propext, Classical.choice, Quot.sound]` and no warnings. The separate
ring-stage packet reports a successful check with unused-simp warnings.
This review did not independently observe those checks. Matching hashes do
not authenticate object source, package, dynamic-load, or transitive
provider ancestry; temporary objects may later disappear. The ring
packet's stale statement that the model bridge was unchecked was corrected
by its author during this review.

```text
cab8f5f58fc5f3bfdb06daa328cdc622fa332fb90608fada0a1706b5cbdb16a9  review.py
dd07a4a06d4ebd449f2692105f3d5135d610421211c5d053e8914d2b6e65689a  result.json
```
