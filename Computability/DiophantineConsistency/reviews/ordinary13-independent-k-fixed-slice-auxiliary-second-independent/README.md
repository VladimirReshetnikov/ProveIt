# Independent review: fixed-slice auxiliary discharge

The reviewed `ordinary13-independent-k-fixed-slice-auxiliary-discharge` packet gives an ordinary-integer construction on the previously pinned fixed compact slice. The proof makes the strong and auxiliary factors +1, and reduces completion by the remaining natural gamma to `H | 2^R−q`. The divisibility remains undecided by this packet, so it does not assert a full zero or establish an iPRA theorem.

The low mask's least digit is `rho−2≡2 mod 4`, q is divisible by four, and `G=q*(beta−K′)−1≡−1 mod 4`. Therefore the actual rank is R≡3 mod 4 and `l=(R−1)/2` is odd. For the selected Pell strong witness, a positive return of its determinant-one matrix modulo c² supplies v>0 divisible by c²; `i=Delta*(v/c²)` is positive, `I=i*c²=Delta*v>1`, and the Pell norm gives `I²=Delta*(f²−1)`.

For the auxiliary root, the odd-index quotient polynomial satisfies `P_0=1`, `P_1=4t−3`, and `P_(l+2)=(4t−2)P_(l+1)−P_l`. The analogous odd Pell ordinates satisfy `Q_0=1`, `Q_1=4A²−1`, and the recurrence with coefficient `4A²−2`. Substitution proves by induction `P_l(1−A²)=(-1)^l Q_l(A)`; evaluation at zero gives `P_l(0)=(-1)^l(2l+1)`. Since I²≡1−A² modulo f² and I²≡0 modulo c, the same odd index R yields `V≡−c (mod f²)` and `V≡−R (mod c)`. As f²≡1 mod c, the moduli are coprime. CRT gives divisibility of `V+f²R+c` by `f²c`, and its positive quotient T satisfies the graph's shifted ordinate equation. The auxiliary Pell norm then gives factor +1.

For necessity of the positive main root, N=67*8807 and R are odd, so q≡2 mod 3, while `a=q³(q+1)`, H and Delta are all 0 mod 3. The positive Pell main root is 2 mod 3 and the graph's reduced signed root is also 2 mod 3; the negative Pell branch is 1 mod 3 and is excluded. The remaining positive branch has exactly the stated congruence condition. The argument keeps the same rank and fixed witness coordinates throughout.

The checker reproduces the author's receipt, independently checks finite coefficient-list instances of the odd-index polynomial identities, the fixed phase and mod-3 parity, and small complete Pell/CRT witness controls. These finite tests do not replace the uniform induction, matrix-period and CRT proofs. No Lean, build, staging, provider replay, arbitrary-model result or iPRA endpoint was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-fixed-slice-auxiliary-second-independent/check.py | cmp - reviews/ordinary13-independent-k-fixed-slice-auxiliary-second-independent/receipt.json
```
