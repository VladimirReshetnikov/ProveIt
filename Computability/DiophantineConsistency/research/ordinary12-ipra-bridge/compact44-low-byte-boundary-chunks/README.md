# Draft boundary-window certificates for the closed MC recipe

`generate.py` produces twelve separate Lean modules, one per remaining
half-open interval after the previously checked periodic, free-gap, prefix
and tail theorems. The intervals contain 142 indices in total, and their
exact endpoints and generated source hashes are recorded in
`observations/generate-attempt01/stdout`. Each proposed theorem states

```
CompactLowByteRecipeData.byteAt j = (lowNat / 256^j) % 256
```

for its interval, using the checked two-digit symbolic window theorem and
bounded case analysis. The source names and interval partition are fixed;
`run.py` is a proposed guarded single-module runner. The generation does
not run Lean or prove that the union of all window results covers the
entire byte list.

At the time this draft was written, **none of the twelve boundary modules
has passed a Lean check**. The closed recipe was externally generated from
the parent payload, but the Python generation/file comparison is not a Lean
theorem about gzip, files or supplement provenance. The sibling
`compact44-low-byte-assembly-draft` is a separate unchecked proposal to
combine future boundary proofs with the already checked interval results.
