# Current South-word shift identities: author receipt

This is an author self-review and fresh Lean replay receipt, not an
independent peer review. Both complete final sources were read.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
| --- | --- |
| `CurrentSouthShift2011.lean` (162 lines) | `256403c28ff13e2fb8585597a1931c1be8703f6726daaf3c5509cfbff5f8cf8d` |
| `CurrentSouthShift2011Checks.lean` (72 lines) | `5fda2aee996501ef7fd24fe6e10498aaf104a1b6846c641a53cfd938aab997e3` |

The main imports are `CurrentCellLabels2011`
(`88698cd0d678d788c169b22915594b9ce37dd5d5c19c3d0069b190e0575f740d`)
and `CurrentCellTranslation2011`
(`c3e9811e9b5c60c8ed740b58277ed40569108f888347ffcbb84169ba31b5685d`).
The checks additionally import the frozen `NativeFieldCycles2011`
(`9cac50de2b83d3b802eab615ab4340027b842abc910586d009c4847b913f8442`).

`southWord c b` is the actual `CurrentCellLabels2011.binaryWord` of the
nine physical digits942..950 in the aligned cell subtype. Its bound512
uses only Boolean digits. `copy_word_translation` sums all nine supplied
physical equalities

`c(b+942+j)=c(b+960+j-t)`

and uses the exact full-modulus cell translation to place their sources
in one cell `theta t b`. No residue representative is substituted for a
full cyclic group coordinate.

The generic `binaryWord_append` and `binaryWord_prefix` split arbitrary
natural coefficient words. Prefix reconstruction uses the Boolean bound
only on the retained low suffix; higher terms disappear as explicit
multiples of the modulus. There is no enumeration of the512 possible
South words or a finite sorting/label cache.

Specializing this generic identity proves:

```
t%2011=19:
S(b) = (2*S(theta t b))%512 + c(theta t b+941)

t%2011=20:
S(b) = (4*S(theta t b))%512
       + c(theta t b+940) + 2*c(theta t b+941).
```

`offset20_error_le_two` bounds the last two terms by2 from the actual
physical selector sum over `Fin 942` in that translated cell. The proof
uses a generic two-entry-subsum inequality, so the two indicators cannot
both be1. No terminal-tile color is used.

The focused checks instantiate both generic prefix identities, verify the
literal offset19 formula, and compose the actual offset20 formula/error
with `NativeFieldCycles2011.offset20_excludes_510`. The composition proves
that no cell's South word can be510 at offset20 under all-cell copy and
physical-count premises, without interpreting any label as a tile color.

Both fresh commands exited0, one process at a time with asynchronous
elaboration disabled:

```sh
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentSouthShift2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentSouthShift2011.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentSouthShift2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentSouthShift2011Checks.lean
```

The final main log `/tmp/current-south-shift-stage2.log` is empty. The final
checks log `/tmp/current-south-shift-checks-stage2.log` contains seven
axiom reports, each limited to `propext`, `Classical.choice`, `Quot.sound`.
Neither source contains `sorry`, `admit`, a new `axiom`, or `native_decide`.

The actual nine copy identities remain explicit premises. Their derivation
from kernel convolution, masks and carries is separate work. The module
does not assume decoded labels, occupation, or whole-field alignment;
nor does it claim the whole equation-to-consistency implication. No
existing frozen source was changed and no commit was made by this author.
