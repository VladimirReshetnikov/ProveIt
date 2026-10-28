# Generic Foundation/HA no-zero sentence bridge — author receipt

Author: `circuit_reduction`; author validation, not independent review. The
complete new source, focused checks, driver and freeze driver were read
before execution. Only new owned files/private links were written. No
frozen source, vendor, shared object, umbrella or Git state was changed.

| Source under `Lean/DiophantineConsistency/` | Lines | SHA256 |
|---|---:|---|
| `FoundationHANoZero.lean` | 170 | `8539882d474478c041177ed90eae788ff02167a7c15621117287e4ab3904eb60` |
| `FoundationHANoZeroChecks.lean` | 117 | `97433dedf7b77313066f353da0c0b0f745bd5579d842c9a7bc62966bdf291919` |

Both final fresh builds passed under `-M6000 -j1 -DElab.async=false`, with
a 512 MiB reserve. The main log is empty. All 27 final axiom reports use
at most `propext` and `Quot.sound`; none uses choice, a custom axiom or
`sorryAx`. Private overlay: `/tmp/foundation-ha-nozero-hmdx_f0v/lib`.
Fresh main object:
`19042e3ae115ea6ce07e9071f8da66e469ade1f0c374190f58b9551d18dcdaf7`.
Fresh checks object:
`79b4852cd82bcc70561d132580133c40736182a985cabee2733c2f1dd0bc8bdf`.
Replay manifest SHA256:
`7df6f5a05338153b6bcda78b825e6191ea5135cdaa0528b88da7987acab3a082`.
Freeze snapshot: `3e7b2306b3cfeba7216759891c1c2252d212b984`.

The main endpoint, `noZero_equivalence e`, constructs an actual
`HA.Proves` proof of the conjunction of both implications between
`FoundationPAHFSyntax.sentence (classicalNoZero e)ᴺ` and
`ArithmeticExpression.noZeroSentence e`, for every `e : Expr (Fin n)`.
It neither assumes nor proves either no-zero sentence. It has no supplied
PA proof, model-truth premise, consistency hypothesis or arithmetic-image
oracle. The concrete current-polynomial instantiation remains separate.

`reflectTerm` accepts an explicit source-variable environment. It sends
zero/addition/multiplication to those source constructors, and successor
to addition of the actual source one. `reflectTerm_correct` proves, by
structural induction on the supplied term, an HA equality between its
interpreted source reflection and its actual target substitution. The
successor case uses the existing genuine HA `add_one`; binary cases use
actual equality congruence. There is no semantic evaluator in that proof.
The distinction is checked explicitly: reflected `S(var13)` is
definitionally `var13 + S0`, not `S(var13)`, but HA proves their equality.

The finite slot environment maps indices below n to the same bound slot,
and maps out-of-range indices to zero. The generic correctness theorem
keeps the required free-variable bound explicit. For compiled expressions,
`ArithmeticExpression.free_term` discharges it from the actual `Fin n`
coordinate. `Term.subst_ext_free` then removes only the substitution that
is the identity on those free indices. No variable is silently captured,
discarded or moved to a different quantified coordinate.

All binary numerals are handled by that same structural theorem and the
existing `binaryNumeral_closed` fact. They are not expanded to unary
numerals, evaluated at their enormous integer values, or normalized to a
different constant compiler. In particular the odd binary branch's
successor and the two successors in its doubling coefficient are covered.

The concrete generic source `classicalNoZero e` uses Empty free-variable
type, n bound slots, a negative equality atom on the two supplied
`splitNatural` expressions, and exactly n applications of universal
closure. It does not use `fvSup` to infer a potentially smaller closure.
Existing GG sends that negative atom to one negation of equality. The
existing embedding and closure identities prove its literal target shape,
without a replacement translation algorithm or a negative-formula DNE.
Neither `splitNatural` nor any fixed large expression is expanded.

Two HA term-equality proofs transport the negated equation in each
direction. The small `all_imp` and `closeN_imp` proofs lift implications
under arbitrary universal closures using a fresh variable and the complete
shifted assumption list. Their input formulas may still contain free
parameters or nested binders. There is no illegitimate generalization over
an unshifted open assumption. The resulting endpoint is an object-language
proof of equivalence, rather than only a metatheoretic equivalence between
truth in the standard natural numbers.

Checks cover the last of fourteen slots, explicit out-of-range behavior,
the successor syntax/proof distinction, the literal small odd numeral,
arbitrary binary numerals, separate bound/free source environments, and
the existing positive-input syntax `var + binaryNumeral 1`. They also cover
zero-variable negative constants, exactly two quantifiers, a negative
control against adding an extra GG double negation, a parameter beyond a
closure count, nested formulas, a zero polynomial, and arbitrary fourteen-
variable inputs. The small numeric syntax check uses kernel reduction;
it does not supply any HA arithmetic proof from numerical truth.

The private cache has 102 selected authenticated modules, including the
same 76 Foundation modules as the accepted order packet. It adds the
accepted `FoundationHAClosure`, `ArithmeticExpression`, and four selected
expression dependencies (`Representation`, `ArithmeticRepresentation`,
`NaturalExpression`, `NaturalExpressionSemiring`). Each selected source
hash matches its accepted record. All selected object/trace hashes and
compiler/package identities were revalidated before/after compilation and
at freeze. The four expression objects agree with both the old source-
identical cache record and the accepted arithmetic compiler record. No
native/current-window module, set-theory model module, broad tactic
umbrella, new Foundation module or prerequisite rebuild was needed.

The inherited metadata pins are:

- Witnesses: `a2de378685941a5072db3f15e54b7f04bbf0833e33b7611f94e328b3a1f9c1ee`;
- Closure: `88cf1f0983335cd29fafcc99fbaea13a6c39033e4d822d9885f81e23aae1bfbe`;
- arithmetic compiler: `432c3b1603952c93cab465c3a07ca939913d84f334331b770a28968261419878`;
- selected expression cache provenance: `afdd946ecf76e6c31da7badf138fffc378080b82f0c2e66b8e33b5fd059edddd`.

Only the selected records of the latter large manifest are reused here;
this is not reuse or validation of its old native closure. One rejected
main attempt is preserved in the replay bundle: it exposed an Empty-variable
proof branch and unavailable negation/assumption helper names. The corrected
source imports the existing negation definitions and constructs assumption
proofs directly; it does not import equality decidability. The next main
and the first checks run passed cleanly. All three invocation records,
complete source snapshots/logs and read drivers are stored under
`reviews/foundation-ha-nozero-author-replay/`.

The literal `ArithmeticCurrentEquation2011.unsolvabilitySentence` is not
imported into this packet. Combining that native expression closure with
Foundation still requires a compatible imported environment; this packet
does not bypass the known duplicate `Matrix.map` issue or refresh that
closure. The final HA equation/consistency equivalence and a classical PA
proof of the corresponding source sentence remain unproved here.
