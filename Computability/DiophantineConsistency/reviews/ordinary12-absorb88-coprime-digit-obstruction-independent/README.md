# Independent audit: 88 coprime-digit diagnostic

**PASS, scoped to the pinned ordinary-integer first-factor diagnostic.** No Lean check or full graph-zero inference is made.

The independently rehashed inputs match the supplied pins: checker `526f8585943af45b363fdbc6dfaa9c41229ee221ad7462a266c8263e17ffefc5`, README `127720ef5fcbef04bdd53ded9fb6bf0021cc1dea61c1bbbe063253c22e2232c0`, receipt `50393f751b8f8616defed8b78cddc005549cfee77b32127f7bafaa8b407bd970`, and pinned DAG `84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25`. Recorded stdout hash `1c42dc156e3530a33e11e40ecdf000966dcd690478f9236b4d324dd6032e945c` and empty stderr hash match. The documented isolated invocation exited 0 and its stdout was byte-identical to the retained output.

An independent evaluator using an explicit operation dispatch evaluated all 88 DAG instructions, whose operations are only addition, subtraction and multiplication. It reproduces b=3, q=4, L=3, G=22, Bt=−228, ell=32768, k=2, Z=98307 and A0=0. It also reproduces A1=127741744268121 and N=25855084223035502305732927033273920, both nonzero. Thus b divides Bt and gcd(b,L+1)=1, but this valuation is not a full zero.

For positive F′, alpha′ and L=3, the strict guard `(F′+alpha′)L+F′<qL=12` implies F′, alpha′ < 4. The complete possible guarded pairs are (1,1), (1,2), (2,1), producing G values 10, 11 and 7 respectively; none equals 22. Equivalently the actual G has remainder 1 and quotient 7 upon division by b=3. This supports the stated obstruction only with G and L fixed and does not rule out a transformation of full graph zeros which changes those quantities.

Negative controls without isolation and with `-I -S -B -O` or `-I -S -B -OO` each exited 1 with the intended message. This audit checks the stated pinned DAG and arithmetic, not its complete historical provenance, the actual full-zero normalization problem, 88/89 existential equivalence, or an iPRA endpoint.
