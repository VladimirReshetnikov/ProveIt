# Equality-free reference certificate format

The top-level value is a nonempty JSON array of record arrays. Variables are
nonnegative integers. Booleans are rejected. Primitive formula arrays:

```text
[0,x,y]          membership E(v_x,v_y)
[1,A]            negation
[2,A,B]          implication
[3,x,A]          universal quantification
```

Record arrays (zero-based references must point strictly backward):

```text
[0,A,B]          A -> (B -> A)
[1,A,B,C]        (A -> (B -> C)) -> ((A -> B) -> (A -> C))
[2,A,B]          (not A -> not B) -> (B -> A)
[3,x,y,A]        (forall x A) -> A[y/x], capture-avoiding
[4,x,A,B]        forall x(A -> B) -> (A -> forall x B); x not free in A
[5,i,j]          modus ponens: i antecedent, j implication
[6,x,i]          universally generalize line i
[7]              generate EC
[8,matrix]       generate pure subset-seeded closure schema instance
[9,i,A]          A, only if alpha-equivalent to line i
```

No assumption or admission rule exists. Theory axioms are closed; theorem-only
generalization is sound. MP compares modulo alpha-renaming. The schema accepts
arbitrary equality-free matrices. Free slot 0 is input, free slot 1 output;
other free slots become universally closed parameters. Every auxiliary binder
is fresh for every label in the matrix. The boundedness premise remains part
of the generated conditional axiom, never a semantic checker oracle.

The designated contradiction is

```text
[1,[3,0,[2,[0,0,0],[0,0,0]]]]
```

A valid certificate may end in a noncontradictory theorem. The checker reports
validity and refutation separately. The identity example is valid and is not
a refutation. Error handling distinguishes malformed proofs from process-level
resource failure; the latter is not silently converted into a negative verdict.
