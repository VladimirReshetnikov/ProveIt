# Static assessment of the 52-step dominated-rho8 proposal

The new derivation is a promising substantive replacement for the private proof hierarchy, but its delivered Lean file is not a drop-in replacement for the current generic API. No supplied producer, search, Lean or Rocq compiler was executed in this review. The raw upstream compilation claims remain attributed claims, not new local acceptance.

The reviewed inputs are the README, complete 402-line renderer and 55-line derivation at `159397838a0af11c030bba140fa5618664cb5a9b`, plus the complete 254-line Lean file at `4fdc59197a45a6beb7e5a4ae7109fd13477b1d17`. `input-review.json` gives their exact byte pins and those of the maintained core/adapter. The original Git bytes are retained beside this note.

## Proof argument and kernel boundary

The derivation has two leaves (truth and restricted rho8) and 52 private MP lemmas. Each displayed Lean body is a direct application of `h.mp` to explicit instances of earlier universally quantified lemmas or restricted rows. Substitution here is ordinary instantiation of proved Lean theorems; no substitution axiom is added to `DomImp`. Side conditions are proved by reflexivity, operand-growth lemmas, a supplied inequality, or four `Nat.zero_le` uses. The last lemma is exactly the unrestricted four-variable row, and `d52 h c u a b` has the required numerical-code order. The statement still quantifies over arbitrary natural codes, including numeric junk.

The renderer's unifier, side-condition elimination and search are outside the proof trust boundary. Incorrect choices can generate a rejected proof, rather than a weaker accepted theorem: all emitted MP applications and inequalities must typecheck. The input parser is permissive (for example duplicate IDs overwrite and leaf classification uses a negative major index), and `--derivation` is not raw-pinned. A maintained production route should therefore bind the exact reviewed input and check regenerated output; it should not treat arbitrary input parsing or the search's optimality claims as a certified checker. The final generic variable-matching guard does not itself establish that every alternate final row supports the hardcoded four-argument wrapper. The exact delivered final row does have the required order.

No emitted body calls `wim00`, uses `simp`, or relies on a syntactic `wim 0 0` collapse. The producer supports such normalization for other inputs, but it is not used by these displayed 52 bodies. This is important for the stronger generic port below.

## Preserving the representation-independent theorem

The present `DominatedImplication.Language` assumes only a reflexive relation closed under insertion in either implication operand. It has no bottom, distinguished zero, injectivity, or `imp τ τ = τ` law. Directly replacing every numeric zero with an arbitrary seed would incorrectly require that seed below arbitrary formulas.

Instead, the four lower-bound uses are local filler choices that disappear from their conclusions:

| Lemma | Replace both local zero occurrences by | Restricted-row guard afterward |
|---|---|---|
| d3 | `wim v1 v2` | reflexivity at `wim v1 v2` |
| d7 | `wim (wim v1 v2) v3` | reflexivity at that formula |
| d10 | `wim v1 v2` | reflexivity at `wim v1 v2` |
| d16 | `v0` | reflexivity at `v0` |

The paired occurrence is the same explicit filler in the major-lemma instance and the minor restricted row. Hence these replacements preserve the exact MP matching and the stated conclusion; all other inequality arguments in those steps are unchanged. The five truth detachments d4/d9/d13/d18/d22 then replace their sole zero argument by an arbitrary `τ`, and apply `h.truth : T τ`. Their major formulas are literally `τ → conclusion`, never an identification of `τ → τ` with `τ`.

All other steps can use the existing abstract `imp`, `below`, reflexivity and growth lemmas. The current `withSeed` construction supplies `τ = rho8 L a a a a` from a reflexive restricted instance, eliminating the temporary truth assumption. This gives a concrete source-level route to the existing truth-free generic rho8 statement, with no stronger language assumptions. It remains an uncompiled proposal. Opening owns the scratch adaptation and must preserve the exact matching in all nine changed bodies.

## API, savings and next check

The historical direct rendering preserves `DomImp`, its three fields, `le_l`, `le_r`, `sub`, `wim00` and `rho8_all`. It removes current `composition`, `lift_right`, `rho8_all_of_restricted`, and the generic core import. Thus copying it over the maintained adapter would lose current statements and the representation-independent result. The minimal safe integration changes the private generic derivation, retains the existing adapter, and explicitly retains or re-derives generic composition and lifting. The old generic tail cannot simply be copied while deleting its referenced helpers.

The delivered numerical file is 11,974 bytes / 254 lines versus the current core-plus-adapter's 22,058 bytes / 454 lines. The arithmetic difference is 10,084 bytes, **not** a measured API-equivalent saving: the generic adaptation and composition/lifting tail still need pricing. This is nevertheless materially larger than the current uncompiled 335-byte inlining proposal and is logically independent of the checked phase9 Home/decoder work. It changes no machine table, source program, calibrated calculus, or external ZFC-consistency statement.

Recommended next step: finish the source-only generic port, preserve every current public header, synchronize a deterministic producer with exact input pins, then perform a bounded isolated kernel/API/axiom check before any adoption. A later combined checkpoint must invalidate by transitive source/import changes, not just equal intermediary object bytes. No new Rocq work is recommended in this Lean-only lane; preserve the checked Rocq production boundary and import the upstream research as provenance.
