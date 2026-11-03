# Unchecked witness-preserving 74 boundary source

These four files adapt the just-author-checked conditional boundary chain, strengthening every conclusion to export the same returned witness's coordinates `w 0 = v 0`, `w 1 = v 1`, and `w 2 = mask`. At the graph level `mask = q p v-v 1-v 2`. This is the missing information needed to establish that the R=31 construction's returned 74 zero actually has `J=F=C=1` and fails `F+C<q`.

The files have **not** been elaborated or kernel-checked; they are a source proposal only. Their assumptions are those of the corresponding conditional boundary chain, and the numeric R=31 Pell inputs remain unformalized. Even if checked and specialized, the selected ports `(1,1,28,0)` are arbitrary ports that violate the fixed BFS bounds. No fixed-port theorem or iPRA conclusion follows.

`Trace74BoundarySeedConditional.lean` is an additional unchecked source proposal specializing to arbitrary ports `(1,1,28,0)`, `J=F=1`, old `alpha=0`, `w=2^30` and `r=15`. It retains the exponential and two finite Pell equations as explicit hypotheses and aims to export a positive 74 zero with returned coordinates `w 0=w 1=w 2=1`. It is not the missing numerical certificate: the audited finite Python calculation has not been connected to those internal hypotheses by Lean. The witness-preserving graph module it imports is itself unchecked.

Independent source-level review passed at `reviews/trace74-boundary-witness-draft-independent/`. It checked the same-witness coordinate equalities and the conditional seed's explicit hypotheses; the files remain unelaborated and no concrete zero is claimed.
