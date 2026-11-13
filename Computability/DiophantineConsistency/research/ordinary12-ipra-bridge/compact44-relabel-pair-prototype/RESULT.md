# Paired finite compact-table correspondence

The reviewed replay actually exited 0 in protected session 43986 at HEAD `172e4b4cb1bd7fff139e76cbcbeb9701da326d26`. All 116 Lean compiler children and direct dependency queries exited 0; corresponding author/peer source, object and log hashes matched. The wrapper reran its three pinned parent audits, array-binding checks and source/HEAD guards before and after the build. Its receipt SHA-256 is `97a9dc8a8806927e8b1694e1083da79d3ce5bd4f9b0af7393b9231fc810972e7`. `terminal-observation.json`, `replay-receipt.json` and all 116 compiler logs retain the evidence; the receipt records 1,190 direct-import companion guards. The largest sampled compiler RSS was 3,046,457,344 bytes.

The final paired Lean theorem is exactly

```
mappedOld = selectedNew ∧
horizontal.toList.Perm (List.range 250) ∧
vertical.toList.Perm (List.range 439) ∧
rowIndices.toList.Perm compactIndices
```

under namespace `CompactRelabelDraft`, where `compactIndices = [0] ++ List.range' 2 941`. It uses the explicit arrays and table definitions documented in the manifest. Both sides report the Lean metatheoretic axioms `[propext, Classical.choice, Quot.sound]`; these are not object-theory iPRA axioms. The relation between these literal arrays and the independently reviewed external permutation/JSON is checked separately, not asserted as a Lean JSON theorem.

This result is provisional until independent artifact review. It does not establish the existence of matching neighbors in arbitrary model tilings, all-model tiling transport, compact44 checker calibration, or a 12-variable iPRA consistency endpoint. The full provider's Foundation wrapper and package-transitive/dynamic ancestry qualifications remain; the monitor is sampled rather than a hard quota, and dependency/audit subprocesses have leader-only timeouts without RSS or descendant-group guarantees. The no-Lean preflight and failed author-only attempts are preserved separately.
