# Independent review of the even-index strong-family obstruction

The pinned obstruction's odd-prime argument, both auxiliary signs, and bindings to the actual parent factors are correct at source level, subject to the stated ordinary Pell classification. For an even main index it excludes the specific strong family `f=x_h`, `i=Delta*y_h/c²` at the same first/main data, for every positive h with `c² | y_h` and all integer R and T. It does **not** exclude other strong witnesses, changed first/main data, or a parent zero, and it is not an iPRA or Lean proof.

The parity argument makes `c` even and then h even, while `f=x_(2k)=2*x_k²-1>1` is odd. For any prime `p | f`, the norm gives `Delta*y_h²=-1 mod p`, so the off-diagonal entries of `Q^h` are units. If an odd ordinate `y_j` vanished mod p, the norm would force `Q^j=±Id`; raising that matrix to the even h gives the identity. The same product in the other order, `(Q^h)^j`, is invertible anti-diagonal, which cannot be the identity. This also handles negative odd indices via `y_(-j)=-y_j`. Hence, for even m and odd ell, the addition identity `y_ell²-y_m²=y_(ell-m)*y_(ell+m)` makes `y_ell` unequal to both `c` and `-c` modulo p.

For the auxiliary classification, `I=Delta*y_h≥3`. The parent equation is `(I*V)²-(I²-1)y²=1`. Standard Pell classification applies to the nonnegative first coordinate `|I*V|` and natural y. The zero index has first coordinate 1, impossible to divide by I; the recurrence gives `x_(n+2)≡-x_n mod I`, with `x_0=1` and `x_1=I`; hence every even-index first coordinate is `±1 mod I` and cannot be divisible by I. Odd indices do have `I | x_ell`. The sign of V can be either sign of this positive quotient, and the odd-quotient identity sends these two possibilities to both signs of `y_ell(A)` modulo p. Since the literal parent requires `V≡-c mod f²`, either sign contradicts the odd-prime result. This explanation covers negative V and does not assume any parity or value for R.

The independent checker compares the eight shared first/main graph expressions and all relevant auxiliary and output rows. It tests the parity and sign identities, traverses complete finite-field cycles with index parity, checks both quotient signs at every odd state for its bounded prime cases, and checks the Pell addition identity with negative indices. These finite tests are controls for the general algebra above, not a proof of Pell classification or a substitute for formal elaboration. The source theorem `ArithmeticPellClassification.solution_index` is pinned for reference; the review does not claim a coherent provider or checked model-level instantiation of it.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-parent-even-main-strong-pell-independent/check.py | cmp - reviews/ordinary13-parent-even-main-strong-pell-independent/receipt.json
```

No Lean, build, staging, nonstandard-model or provider audit was run.
