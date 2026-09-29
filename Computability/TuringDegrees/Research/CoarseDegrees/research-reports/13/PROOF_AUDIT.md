# Mathematical proof audit

## Certification boundary

The manuscript supplies complete conventional arguments. It has not been
independently refereed and has no Lean or Rocq verification. Finite diagnostic
checks and successful typesetting are separate from correctness of the
infinite proofs. No open classical conjecture is assumed in the construction.

## Theorem 3.5: the guarded set's uniform coarse classification

1. The set X is exactly the guarded all-earlier-inputs definition (3.1).
   Do not replace it by an arbitrary complete c.e. representative.
2. The index f(e) waits for all computations of phi_e up to the input, then
   returns zero. Its guarded column is full iff phi_e is total, finite otherwise.
3. A density-zero global error has density zero when pulled back to any fixed
   dyadic column. The column-majority approximation therefore converges.
4. In the domination algorithm the search stage is constrained to be >= n.
   That condition ensures eventual inclusion of every fixed total index.
   False positive approximations can delay termination, but stabilize away
   for each finite group of indices, so the search terminates on every input.
5. Bounded guard simulation makes finitely many errors on each fixed column.
   The dyadic tail bound, not arbitrary countable additivity, yields density zero.
6. Both reductions are ordinary oracle procedures. A jump oracle is used to
   characterize the spectrum, not queried by the coarse transformation.

## Theorem 5.1: the complete countable join

1. Uniform H-computability of P_k and F <=_T H makes finite admissibility
   uniformly H-decidable. At each fixed level local B_k-computability also
   holds, but a uniform sequence of local indices is NOT assumed.
2. A condition has finitely many stems but protects P_k in every coordinate.
   This is compatible with finite computation witnesses and gives a nonempty
   product reservoir. Increasing k after an admissible extension shrinks it.
3. Fixed-oracle disagreement is Sigma^0_1(H). If no witness exists, searching
   admissible extensions in B_k computes any actual common total output.
   H is not used to verify each returned value in that decoding algorithm.
4. Finite-join disagreement uses one finite array. Shared coordinates must
   agree. In the decoding search they are checked against the actual shared
   oracle before compatible finite arrays are amalgamated.
5. N_(i,e) uses an unprotected position and H' to separate the i-th coordinate
   from phi_e^H, unless that function already diverges at the chosen input.
6. The jump requirements explicitly query existence of a finite witness for
   Phi_e^(Z join H)(e), where Z is the ENTIRE countable join. Positive answers
   have permanent witnesses; negative answers remain valid by reservoir
   inclusion. This proves completeness of the jump-decision record.
7. All conditions are finite parameters even when selected using H'. Their
   positive-witness predicates remain H-c.e.; no second jump over H is used.
8. Totality of each coordinate follows from the mandatory growing-length
   steps. Density zero follows by fixing a level, taking the limsup over
   prefix length, then letting the level increase.
9. The lower inclusion of the desired exact ideal uses the explicit
   hypothesis I subset Core(F). It is NOT automatic for an arbitrary profile
   of protected regions; applications verify it separately.

## C4 application

The target F is Turing equivalent to the full profile join H. Robust block
majorities show that every description computes every finite profile join.
This proves the lower inclusion in the core. Exactness of Z with H then
supplies the upper inclusion. Individual computability of each profile
column does not imply computability of their full join. Principal cores
therefore do not automatically give a least representative.

## C6 application and optimality

For X, each finite union of guarded columns is computable nonuniformly.
Take local B_k empty, presentation H=X, and I=Comp in Theorem 5.1. This gives
the upper jump bound and exactness with 0'. Theorem 3.5 independently gives
0'' <= D' for EVERY description D of X. Hence the constructed bounds are
exact equalities. The partner is low over 0', not ordinarily low. X itself
is a Delta^0_2 description; it is exactness with X that rules out a Delta^0_2
partner. No claim about every complete c.e. set follows.

## What remains unproved here

- Bibliographic priority for the extensions.
- Proof-assistant verification.
- The fixed Delta^0_2 1-generic case of C6.
- C2, C7, C8, or the absence of all minimal elements in a coarse spectrum.
- Arbitrarily prescribed computable disagreement-count budgets.
- A uniform computable selector of the guarded section programs.
- A perfect family all of whose members lie below one fixed oracle.
