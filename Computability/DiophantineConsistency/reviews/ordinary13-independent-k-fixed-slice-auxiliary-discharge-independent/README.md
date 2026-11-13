# Independent review: auxiliary witness on the fixed slice

The [reviewed construction](../../research/ordinary13-independent-k-fixed-slice-auxiliary-discharge/README.md) soundly discharges the strong and auxiliary factors over the ordinary integers for the specified fixed-port slice, assuming the preceding slice construction. I found no mismatch in its phase, Chebyshev signs, CRT, positivity, period argument or main-root sign analysis. The resulting if-and-only-if concerns **completion of that constructed slice by a natural gamma**. It does not decide the remaining divisibility, produce a graph zero, or resolve a global zero-map or iPRA question.

The low mask's zeroth base-rho digit is rho−2 and all higher digits are divisible by rho; because rho is divisible by four, MC≡2 mod 4. On this slice q≡0 mod 4 and G=q*t−1, hence `R=G(q²−1)+MC+q*MF≡3 mod 4`. Thus R=2l+1 with l odd, and the quoted n is even.

The main Pell matrix is invertible modulo c² because its determinant is one. There are at most c⁸ residue matrices, so a positive power h≤c⁸ is the identity. Its ordinate v is strictly positive as an ordinary Pell iterate and divisible by c². With `i=Delta*(v/c²)` the graph's I equals Delta*v; the main Pell norm then yields the stated strong equation. Moreover `f²≡1 mod c` and `I≡0 mod c`.

The reviewed recurrences correctly express `x_(2l+1)/I=P_l(I²)` and `y_(2l+1)(A)=Q_l(A)`. Their bases and recurrence coefficients give `P_l(1−A²)=(-1)^l Q_l(A)` and `P_l(0)=(-1)^l(2l+1)`. With l odd and `I²≡1−A² mod f²`, this gives `V≡−c mod f²`; with I divisible by c it gives `V≡−R mod c`. Since `f²≡1 mod c`, the two moduli are coprime. The CRT therefore gives divisibility of `V+f²R+c` by f²c. Its numerator and denominator are positive, so the constructed T is a natural at least one, and its rearranged equality is exactly the child's signed ordinate. The auxiliary Pell norm makes that factor one.

For the positive main root, the displayed H divisibility makes `(g−q−a*c)/H` integral and positive: `g>(a+1)c` follows from `g²=1+((a+2)²−1)c²`, so `g−a*c>c>q`. For necessity, an actual main residual zero forces its signed scaled root d to be g or −g. Here N and R are odd, so q≡2 mod 3, while a and H are divisible by 3. The Pell congruence gives g≡2 mod 3, and the literal root gives d≡2 mod 3; therefore d=−g is impossible. The positive root equation then forces H|2^R−q. With the other three factors fixed at one, this is exactly the condition for this slice's output to vanish.

The receipt reproduces all three cited author receipts, checks the low-digit source, independently generates and compares 16 odd Pell polynomials, finds small positive matrix periods by modular iteration, and verifies CRT/positivity/main-sign controls. These checks do not expand the fixed huge values or replace the uniform integer proof. No Lean, model-provider, axiom or PDF validation was performed. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-fixed-slice-auxiliary-discharge-independent/check.py | cmp - reviews/ordinary13-independent-k-fixed-slice-auxiliary-discharge-independent/receipt.json
```
