# Independent source review: direct 85 P72 first inputs

The two source clients use the same positive 85 valuation, graph zero, port
casts and natural rank. Their q definitions agree. The direct rank window
gives R≥40 and the required `R+1<q⁴`, and only the rank-side remainder is
removed. The existing first-index and residue witnesses are retained; no
q-divisibility of X is required.

The checker pins the source interfaces, replays author and independent
dependency receipts, and tests finite modulo inputs including `2n≥q⁴`.
This is source and finite review only: auxiliary and main P72 alignments,
exact indices, Lean elaboration, provider compatibility, external-file
binding and iPRA remain open.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-85-p72-first-inputs-draft-independent/check.py > /tmp/p72-first-inputs85-independent.json
cmp /tmp/p72-first-inputs85-independent.json reviews/ordinary14-85-p72-first-inputs-draft-independent/result.json
```
