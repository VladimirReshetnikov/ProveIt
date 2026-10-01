# Proof status

## Established in this note

- Exact unit-activity pendant length-two arm identity for matching supports
- Exact support polynomial and tail-deficit formula for the constructed family
- A connected all-unit bipartite counterexample of matching rank 3450
- Corresponding degree-normalized ULC failures and nonreal zeros for the
  edge polytope of the two-vertex augmentation and the stable set polytope
  of the complement, by Davis–Kohl Theorem 3.10 and Lemma 3.11
- A connected all-unit counterexample whose matching rank is one below the
  smaller shore size
- An infinite family of deficiency-one counterexamples by an explicit
  asymptotic sign calculation followed by finite integer choices

The main certificate is

    Delta_3449 = -314102056577041236 * D^2 * 191^6 < 0
    D = 160160547610973088925200

Every vertex activity is 1. The number 191 is one plus the number of
pendant arms at each designated vertex; it is not a vertex activity.

## Verification

The written proof is supported by independent exact endpoint-set tests of
the gadget, two independent tail computations, explicit matching/cover
checks, and independent human-readable mathematical audits. The final PDF
was rendered and visually checked on all five pages. Finite tests and a
successful build are not substitutes for the general counting proof.

## Not established

- The smallest possible matching rank, vertex count, or edge count of a
  unit-weight counterexample
- Failure of the published smaller-shore normalization
- Failure of ordinary log-concavity
- Worldwide priority
- Formal verification in Lean or another proof assistant
