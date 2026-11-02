# Bounded one- and two-gate screening for the 13-variable equations

The [independent review](../../reviews/frontier13-local-rewrite-screen-independent-audit/README.md)
reproduced the bounded enumeration and checked the finite-field rejection
argument and degenerate cases. Its limits below remain essential.

For each of the pinned 87-operation square-sum and 86-operation product DAGs,
`screen.py` examines the following **restricted** syntactic family:

1. Select one existing gate as target. Its replacement may use only the
   original inputs, literals `0, 1, 2, 3, 4`, and gates earlier than that target.
2. Replace that gate by an earlier node, one binary `+`, `-` or `*` gate,
   or two such gates. For two gates, the second must use the new temporary,
   either with an earlier node in either applicable order or twice.
3. Keep every other row and the output unchanged. Count live binary gates
   after deleting all dead rows. Seek a strict count reduction while preserving
   the **target polynomial** over the integers with all four ports symbolic.

The certificate finds no strict candidate in this family for either graph.
It includes temporary signatures that duplicate an earlier node, the case
where the final operation uses the temporary twice, literal zero and one,
both subtraction orders and all sampled possible zero/one gate identities.
An earlier screen of a different 87-gate graph explicitly omitted some of
these cases; this packet does not rely on that exclusion.

The filter evaluates each graph on three deterministically generated tuples
modulo `2305843009213693951`. It exhaustively compares all operations in the
declared family against the target signatures and computes their resulting
live counts. Any integer-polynomial identity valid for all variables and ports
must agree at these tuples; therefore, if the program enumerates this family
correctly, the absence of a signature match with a lower live count rules out
an exact same-target identity in this family. Sample matches are **not**
promoted to identities. Product lookups fail closed if any nonzero earlier
signature component is not invertible; multiplying by literal zero cannot
match because every sampled target is checked nonzero. The output reports all
sample matches, including false positives, and there are no sampled aliases.

This is not a global operation lower bound. It does not cover three or more
replacement gates, changed earlier rows, compensating changes to downstream
rows, alternate positive-witness encodings, polynomial equality only after
specializing the enormous fixed ports, equality of zero sets without polynomial
identity, or other free constants. It is finite external reasoning, not a Lean
theorem or proof that either equation is minimal. The two target graphs and
their source hashes are pinned in the script.

The two small positive controls include a cancellable expression that has
strict one- and two-gate improvements and a case detected when the second gate
uses the temporary twice. `run.py` records both the actual normal exit and the
deliberate `python3 -O` rejection; it refuses to overwrite `receipt.json`.
Run `python3 screen.py` for a read-only rerun, or run `run.py` in a copy that
does not contain the recorded receipt. These controls check the search harness;
they are not proofs about the ZFC equations.
