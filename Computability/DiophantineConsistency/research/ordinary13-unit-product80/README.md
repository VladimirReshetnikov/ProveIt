# Thirteen-input unit-product finalizer: 80 operations, degree 99

This **proposed** graph has 13 positive inputs, 80 live arithmetic operations
and exact degree 99 at the authenticated compact44 ports. It replaces the
four-square finalizer of the reviewed
[`13/81` residue-first parent](../ordinary13-residue-first81/) with a product
of four integer-unit factors. Their zero sets agree at **every integer
valuation and arbitrary integer ports**, not just positive inputs. The local
unit argument and degree certificate below are submitted for independent
review. No new Lean/iPRA theorem, PDF/JSON binding, fresh provider replay or
global minimum is claimed; the parent's compact44 endpoint and source
qualifications remain inherited.

## Integer zero equivalence

The parent output is

```
A0² + A1² + (Fa−1)² + g72²,
```

where `A0=Z²−b²*(1+ell*(ell+k))`,
`A1=Dstar²−U²*(1+Delta*c²)`, `g72=I²−Q`,
`Q=Delta*(f²−1)`, `I=i*c²`, and
`Fa=y²−Q*(y²−V²)`. Replace its eight-gate finalizer by the seven-gate

```
F0=1+A0, F1=1+A1, Fs=1+g72,
out = F0*F1*Fa*Fs−1.
```

Each of F0, F1, Fa and Fs is never −1 modulo 4 at **any integer input**:

1. For F0 write `q=b+1`, `Y=q³*s`, `ell=X*Y²*k`. If b is even then
   `F0=1+Z² (mod 4)`, which is 1 or 2. If b is odd then q is even, so
   Y is divisible by 8 and ell by 4; hence `F0=Z² (mod 4)`, which is 0
   or 1. No positivity or fixed-port hypothesis is used.
2. `Delta=a²+4a+3` is 0 or 3 modulo 4. It follows that
   `U²*(1+Delta*c²)` is 0 or 1 modulo 4, and `F1` is 0, 1 or 2.
3. Both `Delta` and `f²−1` are 0 or 3 modulo 4, so Q is 0 or 1. Thus
   `Fa` is congruent to `y²` or `V²`, and is 0 or 1 modulo 4.
4. Since `I²` and Q are both 0 or 1 modulo 4, `Fs=1+I²−Q` is 0, 1 or 2.

If the product output is zero, the four integer factors multiply to 1.
Each is therefore +1 or −1, and the exclusions force all four to +1.
Consequently `A0=A1=0`, `Fa=1` and `g72=0`, so the parent's sum of squares
is zero. Conversely, a zero of that sum has these four equalities and
therefore makes the product output zero. This argument does not use a
positive domain, q nonzero, beta nonzero, or the compact44 calibration.

## Exact count and degree

The source removes the parent's eight finalizer gates and adds the seven
displayed factor/product gates, giving `81−8+7=80`; all 13 inputs, four
fixed leaves and all gates are live. At fixed ports, write

```
Z=b*ell+delta,   delta=b*(k+r−k*Bprime)−Bprime.
A0=2*b*ell*delta+delta²−b²*(1+ell*k).
```

The source bounds `deg(b*ell)<=12` and `deg(delta)<=5`, so `deg A0<=17`.
The reviewed main-residual cancellation gives `deg A1<=30`, while
`deg Fa<=30` and `deg g72<=22`. Hence the four-factor output has degree at
most `17+30+30+22=99`. The full authenticated all-inputs-equal ray modulo
1,000,000,007 has degree 99 with leading coefficient 663418019, proving exact
specialized integer degree 99.

The checker pins both full graphs and P72/P115 port bytes, verifies the exact
source delta/topology/liveness, tests signed graph evaluations and exhausts
finite modulo-four controls for the displayed exclusions. These controls do
not replace the all-integer argument or degree proof above.

```
python3 -I -S -B research/ordinary13-unit-product80/check.py > /tmp/unit-product80.json
cmp /tmp/unit-product80.json research/ordinary13-unit-product80/result.json
```

Independent external review is recorded in
`../../reviews/ordinary13-unit-product80-independent/`.
