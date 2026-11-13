# Standard-iPRA client provider survey

This is a no-Lean, point-in-time comparison for the **uncompiled**
[`IPRAStandardQM40` draft](../draft/IPRAStandardQM40.lean). It does not
establish the native retry's outcome, a coherent combined provider, a
standard-theory endpoint, a matched replay, or a PDF binding. The native
retry was still running when the scan was made; the scan deliberately uses
only its pre-existing seed, not any potentially partial output.

The proposed standard source imports `IPRAStandardTheory`, `IPRAQM40Native`
and `IPRABoundedRhoZFC`. The historical standard overlay retains its compiled
`IPRAStandardTheory` and three predecessor objects, but many of its inherited
objects are dangling symlinks into the now-absent
`/tmp/ipra-aq29-fresh-project-pair/author/lib`. Thus the historical overlay
cannot currently serve as a complete provider by itself. In particular, its
symlinked `IPRANativeTheory` and `IPRABoundedRhoZFC` are unavailable there;
the quartic seed does contain an `IPRABoundedRhoZFC` object.

Following recorded direct imports in the pinned historical author state, the
four standard-presentation additions have three project boundary objects and
`Init`. At this observation their recorded hashes compare as follows:

| Boundary | Historical recorded `.olean` SHA-256 | Quartic-seed/package SHA-256 | Result |
| --- | --- | --- | --- |
| `IPRAAddOneDirect` | `34016e7d69ee2a8a1c7ed44132ef49b9b9cacf06c4117625c543885d26df32c3` | `1376c02bb883d6d70a26f569bc49a2d62a04d614f3ca342885eb9340a9496449` | different |
| `IPRAEqualitySymmetryGG` | `373cddc30b30bea88569e9ac2f66d9f9b44f93b24056f605c3c1043ec5fedcc0` | `373cddc30b30bea88569e9ac2f66d9f9b44f93b24056f605c3c1043ec5fedcc0` | match |
| `IPRAOpenDisjunctionWitness` | `5f139f9dde89d15c185fcfbc71252369bb11657b5f88ef81dcde7bec95b0fabf` | `5f139f9dde89d15c185fcfbc71252369bb11657b5f88ef81dcde7bec95b0fabf` | match |
| `Init` | `d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e` | `d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e` | match |

For the three project boundaries, all nine recorded non-olean companion slots
were absent both historically and in the selected quartic seed at the scan.
The historical state's project overlay guards did not record the package
`Init` companion slots; the current package has `.olean.private`,
`.olean.server` and `.ir` companions, so their historical agreement is
**unknown**. The old project `.olean` links are currently dangling: the old
hashes above come from the pinned historical receipt, not a fresh read of
those missing files. A different `.olean` hash does not by itself prove
that the Lean theorem statements differ, but it means direct object reuse is
not authenticated by this comparison.

## Candidate same-provider sequence

After the native retry actually passes, make a separate fresh overlay of its
completed provider and do not overwrite that provider. Rebuild the following
historical standard sources in order against the quartic provider:

1. `IPRASuccessorInduction`
2. `IPRAAddOneGeneral`
3. `IPRASuccessorInductionConverse`
4. `IPRAStandardTheory`

The scan verifies these four current source hashes against their respective
historical author-run hashes and checks that their target companion slots
were absent from the quartic seed and package at scan time. This is the
smallest extension identified by the **recorded direct-import graph**; it is
not proof that recompilation will succeed against the different
`IPRAAddOneDirect`, nor a full transitive closure analysis. The runner must
recheck target slots and source hashes at launch, freeze sources, resolve
`lean --deps` on the actual overlay, guard all direct candidates and
companions before and after each child, and record all compiler exits,
diagnostics, axiom reports and object hashes. Then build the standard draft
against the same rebuilt objects and the actual completed native output,
checking its three printed axiom reports. Use bounded resources and preserve
all failures. A successful author-only run would retain the native model,
historical parent, project-transitive, package-transitive and dynamic-load
qualifications; further independent replay and display binding remain.

`scan.py` ran without Lean and produced [scan.json](scan.json); a second run
matched byte-for-byte. Optimized Python was rejected. The initial scanner
expected the wrong historical status label and exited 1; it was corrected to
the receipt's actual `AUTHOR_ONLY_PASS` before the successful scan. The
historical receipt is SHA-256 pinned in the scanner. All comparisons and
absence checks are point-in-time; the scan does not monitor changes between
observations or inspect the actual native retry's eventual output.
