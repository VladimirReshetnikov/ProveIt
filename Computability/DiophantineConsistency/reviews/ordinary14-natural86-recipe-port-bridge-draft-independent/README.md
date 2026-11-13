# Independent source review: natural86 closed recipe ports

The source interfaces pass this bounded review. The existing natural-valued
base-256 tuple decoder is cast to integers and `byteP_eq` identifies it with
the exact symbolic tuple used by the proposed natural86 endpoint. Its fourth
entry is `betaNat + highNat` once. The new expression differs from the old
one only by that port tuple; the proposed bridge and native, standard and
equality-only statements retain the same types and mapped-refutation sides.
No additional positive shift is introduced. The author checker and receipt
reproduce, and this checker pins the individual decoder source files, symbolic
tuple sources, endpoint, author packet and original author README.

This is a source review, not Lean elaboration, object/provider coherence,
axiom replay, an established iPRA result or a theorem about external gzip,
raw, JSON or PDF bytes. The historical recipe theorem and the previously
proposed endpoint remain dependencies with their own scopes; this review does
not replay their complete dependency chains. Exact rewrite behavior and
transitive imports require actual Lean verification under the project guards.

Run from the project root:

```
python3 -I -S -B reviews/ordinary14-natural86-recipe-port-bridge-draft-independent/check.py | cmp - reviews/ordinary14-natural86-recipe-port-bridge-draft-independent/result.json
```
