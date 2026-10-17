# Internal reindexing of two newly bound labels

`ModelCodedBindTwoSlots` proves an exact syntax identity for arbitrary internal
formula codes, binder depths, chosen labels and target bound indices. It
supports the later Collection client; it does not prove the numerical G row.

For `a != b` and `IsSemiformula L d p`, the checked identity is

```
subst L (twoSlotVec L d i j)
  (bindOneAt L b (d+1) (bindOneAt L a d p))
= bindOneAt L b (d+j) (bindOneAt L a (d+i) p).
```

`twoSlotVec L d i j` is `qVecIter L d [bvar i,bvar j]`. Its fixed Sigma1
graph is chosen before the arithmetic model. The vector has source length
`d+2` and the safe target bound `d+(i+j+1)`, fixes each old slot below `d`,
and maps the new slots `d,d+1` to `d+i,d+j`. The target indices may coincide
and may be nonstandard. Only the chosen-label condition `a != b` is assumed.

The vector specification uses internal Sigma1 induction. The term and
formula identities use eligible Pi1 structural induction, keeping all four
parameters `a,b,i,j` universally quantified as each formula quantifier
increases the old depth. The proof never enumerates an internal code or
internal arity as an external finite datatype. A formation upcast handles
unused target slots without importing the decoder's larger closure.

The three intended Collection uses are target vectors `[1,0]`, `[2,0]`, and
`[0,1]`. The middle case explicitly accounts for a bound slot belonging to an
outer variable that the inner witness matrix does not use. Same-label
absorption, container-label freshness, the zero-code case, and coincident
chosen labels belong to separate actual G-client obligations.

The focused Lean4.32.0 check passes 8 ordered axiom reports and 12 callers,
with only `propext`, `Classical.choice`, `Quot.sound`, and zero warnings. The
source took 10.971 s and the audit 2.222 s. The exact guarded closure contains
ten existing project objects, six external source/object boundaries or
explicit dependency-discovery anchors, and actual Init/Std/Lean/Omega
providers; all 46 input/provider and fresh-object postchecks pass. Only the
new module and audit are built. No dependency build/download, whole-cache
attestation, or resource increase is claimed.

The first failed attempt is preserved with its diagnostics. Its four errors
were arithmetic-bound and equivalent-depth normalization issues; the
reviewed repair changes no theorem statement or induction. Only the second
attempt is the full PASS. The original guard and each preparation are
retained separately; preparations are explicitly unbuilt, although they
query `lean --version`.

From the repository root, using the pinned dependency checkout and recorded
cached objects:

```sh
python Logic/Interpretability/ZFCinPA/check_model_coded_bind_two_slots.py \
  --repo "$PWD" --dependency-root /path/to/pinned/Proofs \
  --output /external/fresh-output
```

`--prepare-only` checks the setup without proof builds. Source, audit,
BindOne evidence/cache, Foundation namespace cache, compiler, and library
paths have explicit relocation flags. Proof runs retain 4 GiB, one Lean
thread, and the ordinary default heartbeat limits.
