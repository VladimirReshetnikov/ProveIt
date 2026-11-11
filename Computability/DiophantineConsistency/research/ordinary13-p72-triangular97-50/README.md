# P72 thirteen-positive triangular residuals: 96/50 and 97/50

This source-only packet gives two pointwise zero-equivalent transformations of the P72 thirteen-positive, 98-operation degree-28 graph. The better variant has **96 live binary operations and exact total degree 50**; the intermediate has 97 operations and degree 50. Each uses the same 13 positive inputs and four fixed compact44 ports as the P72 graph. A previously known 13-positive **93-operation, degree-34** P72 predecessor dominates both points in operation count and degree; these are structural examples, not a new Pareto improvement or a replacement for that predecessor.

The inherited P72 source has an author-side Lean iPRA endpoint, described in `research/ordinary13-p72-endpoint/README.md`, with the file and build qualifications there. This packet establishes the displayed transformations externally; it does **not** contain a new Lean theorem, a formal binding of either JSON file or PDF, an independently rebuilt foundational ancestry, or a proof of either side of the consistency biconditional.

## Fixed inputs and cost convention

Write `b = 3*beta`, `b2 = b²`, `L = beta*b2`, and `L2 = L²`. The P72 fixed `beta` is `2^590069−1`, hence `b2>0`. As in the P72 cost convention, integer constants derived solely from the four fixed ports are computed in advance and available as free leaves. In particular this packet adds the derived leaf **`L2`**; the original `Kfinal=b2*L²` is no longer live. If computing `L2` from `L` is charged as an operation, each stated count increases by one. This is an integer-leaf circuit convention, with no new coordinate or independently variable parameter.

The positive inputs are `F, alpha, C, f0, i, T, X, Y, r, eta, zeta, u, gamma`. The source has

```
a = X*Y + Y,        Delta = a² + 4a + 3,
c = (eta+zeta)*Y + eta,   I = i*c²,
f2m = f2-b2,        Vhat = f2*(beta*c*T-Rhat)-L*c,
yhat = Vhat + L*u,  gap = yhat² - Vhat².
```

For every allowed input, `a>0` and `Delta=(a+2)²−1>0`. These inequalities hold before any equation is assumed.

## Exact transformations and both directions

The original P72 residuals are `A0`, `A1`,

```
As = f2m - b2*Delta*I²,
Aa = b2*yhat² - Delta*f2m*gap - b2*L².
```

The original output is the sum of their four squares. Set

```
Aa_new = yhat² - Delta²*I²*gap - L².
```

The exact integer-polynomial identity, with no divisions, is

```
b2*Aa_new = Aa + Delta*gap*As.
```

For the 97-gate variant retain `As`; for the 96-gate variant use `As96 = Delta*As`. Since `Delta>0`, `As96=0` iff `As=0`. On either strong-zero locus the identity becomes `b2*Aa_new=Aa`; since `b2>0`, `Aa_new=0` iff `Aa=0`. Thus the original four residuals vanish together iff the new four vanish together, at **each same positive valuation**. A sum of integer squares is zero iff every square is zero, giving both directions for the full output. No positivity of an auxiliary expression or choice of a new witness is needed.

The 97-row graph computes `g25=Delta*I²` and `g85=Delta*g25`. The 96-row graph reorders the already-needed `g71=Delta*c²` before the strong block and uses

```
j = i*g71;  g85 = j²;
As96 = Delta*f2m - b2*g85.
```

Then `g85=Delta²*I²` and `As96=Delta*As`, exactly. Relative to the 97-row graph, the six original strong/auxiliary multiplications and subtractions are replaced by five, saving one operation while retaining `g71` for `A1`. The outputs are `A0²+A1²+Aa_new²+As²` and `A0²+A1²+Aa_new²+As96²`, respectively.

For both graphs the difference of squares is evaluated exactly as

```
gap = (L*u)*(yhat+Vhat),
```

using the already computed `L*u`. This factorization is essential to the direct syntactic degree upper bound; expanding the two squares independently would obscure their leading cancellation.

## Reproduction and limits

From the repository root run:

```
python3 -B Computability/DiophantineConsistency/research/ordinary13-p72-triangular97-50/check.py
```

The deterministic output is `result.json`. The checker pins the original graph, proof and active byte binding; reconstructs both proposed schedules; checks every dependency and all 96 or 97 gates live, including all 13 coordinates and four original fixed ports; proves the two elementary identities in an exact sparse integer-polynomial ring; and checks the four actual compressed and raw port hashes and lengths. The port bytes use P72's little-endian encoding, and the already-shifted MF port is used unchanged.

A syntactic pass through all operations gives upper degree 50 for each proposed graph, with `gap` degree at most 7 and `Aa_new` at most 25. Evaluation of the **whole proposed graphs** with all 13 witnesses set to `t`, using the authenticated actual port values modulo 1,000,000,007, gives degree 50 and nonzero leading coefficient 148237445. The auxiliary degree-25 leader is 370278151, also equal to `1728*beta*L*(b+3)²` modulo the same prime. The modular ray supplies a lower bound for the specialized integer polynomial, so together these checks establish exact degree 50 at those bytes. This is an external calculation, not a Lean `totalDegree` theorem.

The pinned upstream proof is the source for the inherited P72 result; this packet's checker does not reprove that proof's machine, arithmetic, or foundational claims. No global optimality is claimed.
