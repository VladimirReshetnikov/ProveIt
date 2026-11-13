# Independent review of the conditional parent lift

The source-level mathematical argument in the pinned [conditional CRT lift](../../research/ordinary13-shifted-two-norm-parent-crt-sufficient-condition/README.md) is consistent with the actual shifted-zeta parent and two-norm graphs. No concrete error was found in the explicit period, CRT conditions, auxiliary signs or input positivity. This is a **conditional sufficient construction**, not an unconditional zero map: the same main ordinate must have an index `m≡3 mod 4`, and a positive `h` with `c² | y_h(A)` must also satisfy `gcd(4h,c) | R-m`. Neither condition is established for every two-norm zero. No Lean or nonstandard-model proof has been checked.

For the period, write `B=[[0,Delta*v],[v,0]]` where `f²-Delta*v²=1`. Modulo `f²`, the Pell matrix satisfies `Q^(2h)=-Id+2fB`, whence `Q^(4h)=Id-4fB`; raising this to the `f`th power gives the identity because all remaining nonconstant terms are divisible by `f²`. Also `c² | v` implies `f²≡1 mod c`, so `gcd(f,c)=1` and the CRT compatibility condition is exactly the stated gcd condition. Taking a larger solution `L` preserves both residues and makes `L≥m≥3`.

For the auxiliary signs, the odd-index polynomial `P_j(t)=T_(2j+1)(sqrt(t))/sqrt(t)` has integer coefficients and satisfies `P_0=1`, `P_1=4t-3`, `P_(j+1)=(4t-2)P_j-P_(j-1)`. The corresponding odd Pell ordinates in parameter A satisfy the transformed recurrence, yielding `P_j(1-A²)=(-1)^j y_(2j+1)(A)`. The same recurrence at zero gives `P_j(0)=(-1)^j(2j+1)`. Since `L≡3 mod 4`, the signs are negative at both moduli. The two CRT congruences therefore yield `V≡-c mod f²` and `V≡-R mod c`, as required. The norm identities show `i` is a positive integer. The graph's first norm excludes `J=0` and `C≤0`; with nonnegative ports this makes its actual rank positive, so the constructed integral `T` is at least one. The odd Pell auxiliary supplies the square-root input `y` as an actual natural integer.

The independent checker compares all eight shared first/main expression trees and all relevant parent auxiliary/product rows, verifies polynomial recurrences and period identities on finite controls, and checks a nontrivial fact-level toy with `m≠R`. These checks corroborate the displayed general proof; they do not replace it or show that the toy is a graph zero. The checker pins the reviewed text, source and receipt as well as both graph JSON files.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-shifted-two-norm-parent-crt-independent/check.py | cmp - reviews/ordinary13-shifted-two-norm-parent-crt-independent/receipt.json
```
