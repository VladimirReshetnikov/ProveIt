# Independent review: shared-Pell 608 and the self-bounding factorial

**Accepted at the ordinary mathematical level.** The self-bounding
factorial lemma is sound in both directions, including the initially
zero proposed output. I found no ordinary gap in its common Pell/radix
composition, source reduction, terminal elimination or integer guards.
Complete normal and optimized replays passed. No Lean was run or edited.

The archive is `docs/incoming/ConZFC_Shared_Pell_608_2026-10-23.zip`,
SHA256 `7782ba5510499c8925e3ca6895dc6ac71ecc6ea7cd85727fc95f6dc760dbdcc2`.
It has 79 members; all 78 manifest entries match. The archive is unchanged.
Scratch review/replay root is `/tmp/proofs62ff-shared-pell608-review`.

| Domain | Variables | Residuals | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| Natural | 608 | 491 | 4 | 7,582 | 79,824,571 |
| Integer | 1,685 | 850 | 4 | 12,082 | 79,827,802 |

These materialized points are already dominated respectively by the
reviewed synchronized596 natural point and the new integer1298 point.
The important reusable contribution is the factorial-radius lemma:
it removes one power call per factorial without using its intended
output as an unproved hypothesis. Here that leaves 25 power calls and
20 exponent groups, compared with synchronized522's 27 and 22.
Combining that lemma with the smaller synchronized engine requires
regeneration and a new dependency/positivity argument; the 608 artifacts
are not a literal replacement for that engine's different source/frame.

## 1. A complete proof of the factorial-radius lemma

For natural n,f put

```
rho=f*n^2,    C=binom(rho+n,n),    P=(rho+1)^n.
```

Then C,P>=1. The two retained natural rows

```
P+C=C*f+r+1,    C=r+s+1
```

are equivalent to `f-1<P/C<=f`. Thus they force f>=1 and say exactly
`f=ceil(P/C)`. For the reverse implication choose
`r=P+C-C*f-1`, `s=C-r-1`; the strict/weak ceiling bounds make both
witnesses natural. In particular f=0 is excluded by the rows, rather
than assumed away to justify the radius.

When n=0, C=P=1 and the equivalence is f=1=0!. For n>=1 and f>=1,
rho>=1. Let F=n!. The exact ratio is

```
R=P/C=F*product_(i=1)^n (rho+1)/(rho+i).
```

Every factor is in (0,1], so `0<R<=F`. Write
`d_i=(i-1)/(rho+i)`. Then `0<=d_i<1` and

```
sum_i d_i <= n(n-1)/(2rho) < 1/(2f).
```

The standard finite product inequality
`product_i(1-d_i)>=1-sum_i d_i` therefore yields the **strict** bound

```
R>F*(1-1/(2f)).
```

For soundness, f=ceil R and R<=F imply f<=F because F is an integer.
Also R<=f and the strict lower bound imply

```
F < f/(1-1/(2f)) = f+f/(2f-1) <= f+1.
```

The denominator is positive since f>=1. The final equality case f=1
is harmless because the preceding inequality is strict. Since F is an
integer, F<=f, and hence f=F.

For completeness set f=F. The same bound gives `F-1<R<=F` (indeed
`R>F-1/2`), so ceil R=F and the displayed natural witnesses exist.
This proves the lemma for all n,f without numerical bounds.

A merely linear radius is unsafe: at n=4,f=23, rho=f*n gives
`ceil(P/C)=23`, although 4!=24. The supplied quadratic radius rejects
this false fixed point. The independent controls preserve that example.

## 2. Positivity and dependencies do not assume the factorial output

The source calls factorial only at its positive trace length and positive
CRT height. For every positive factorial input n, even if candidate f=0,

```
rho+n>=n>=1,    rho+1>=1.
```

Thus its binomial has positive upper/lower arguments and its numerator
power has positive base/exponent before f is identified. The checked
macro order never marks a binomial output positive, and treats each
factorial output as having lower bound zero until its ceiling lemma
applies. This is sufficient for the actual 25 calls.

The shared digit limit is an independent natural parameter `L=L0+1`.
Its first power is `2^L`, and q is that output plus one. A retained row
sets L equal to the sum of all 14 actual binomial upper arguments.
Consequently each upper argument is <=L on every natural zero, without
assuming that a candidate factorial is already correct. Pointwise power
calibration followed by the no-carry base-q digit theorem identifies
the binomial for such inputs; the self-bounding lemma then identifies
the factorial output.

Completeness first chooses the true source/CRT values and true factorial
outputs, including rho=n!*n^2 for each factorial. These determine all
binomial upper arguments independently of L. Set L to their sum and
choose the digit powers and quotients. Only then choose the common Pell
frame and index witnesses. The exact semantic-dependency audit checks
that no private Pell coordinate enters these arguments. Abstracting a
factorial by its proved function of n removes its internal self-reference;
this abstraction is justified by the lemma in Section 1, not an assumed
unique fixed point.

## 3. The 608 shared frame is different from synchronized522

Here the frame is `W=sum_calls(n+k)`; proposed outputs are not included.
Z is an unshifted natural. Every power retains its own strict gap
`T=m+gap+1` and definition `2An=T+n^2+1`.

The first call has base 2, positive exponent L, and `4A=T+5`, T>=1.
It forces A>=2 using only ordinary rows. The frame has W>=3 and bounds
every requested n,k. Its final norm gives
`A^2=1+W^3(W+2)Z^2`; now A>=2 excludes Z=0 and gives A>W. Natural
subtraction A-n agrees with ordinary subtraction. Each positive call
therefore satisfies all hypotheses of the inherited power criterion,
including its original output gap. That criterion supplies the required
exponential soundness bound internally; no argument infers n^k<A from
only the weaker inequality A>W.

For simultaneous completeness, choose `A=chi_(W+1)(W)` and
`WZ=psi_(W+1)(W)` after all true bases/exponents are fixed. For the true
index pairs, a common auxiliary index

```
M=2*product_i(k_i*Y_i),    U=chi_A(M),    V=psi_A(M)
```

works. The Pell divisibility identities give `Y_i^2|V`; the even index
makes V even, and the norm makes U odd and coprime to V. Thus U is
coprime to `4 product_i Y_i`. CRT supplies the common B in the classes
`A mod U` and `1 mod(4 product_i Y_i)`. The chosen U>A makes its ordinary
natural representative B>=A. The canonical coordinates at B satisfy
the S and R congruences, with natural quotients by monotonicity.
Each original individual index criterion is restored. The corresponding
auxiliary product is used only to prove existence; it is not a hidden
coordinate of the exported polynomial.

The oriented power quotient is justified by the Pell recurrence, or by
the positive congruence difference
`n*psi_A(k)-psi_A(k-1)>0` together with the strict output gap. Sharing
the frame and indices does not require independently chosen witnesses
to agree without a simultaneous construction.

## 4. Source, eliminations and integer signs

The numerical-calculus source and expanded wire JSON are byte-identical
to the immediate shared-certificates source before the two beta remainder
rows are deleted. A complete AST comparison confirms that these are the
only changes in `direct_calculus.py`. Bounds S,Sp<=y recover strict beta
remainders; completeness chooses a cofinal beta scale after the finite
accumulator states. The schema/quotient bound here remains `V=m+y+U`,
unlike synchronized522's bound pattern. Its envelope covers all those
inputs and the actual source pair.

The independent affine checker verifies every original nonnegative
triangular gate definition. The terminal checker replays exact monic
substitutions and checks every consumer is linear in its eliminated
coordinate, preserving degree two. Both natural and integer lifts are
therefore justified.

The integer companion guards all 359 original free inputs using
`8x+3=a^2+b^2+c^2`. It forces integer x>=0; Legendre supplies witnesses
for all natural x because 8x+3 is 3 modulo 8 and not exceptional. It
does not rely solely on a `kind` annotation: the independent checker
identifies the raw free inputs from the complement of the actual gate
definitions, confirms every one survives and is guarded, and verifies
all inverse affine/terminal substitutions. Restore the raw integer
system algebraically first, then use topological nonnegative gate
induction from those guarded free inputs. One need not assume retained
gate values nonnegative while restoring them. This order closes the
otherwise possible sign gap.

## 5. Provenance and exact replays

Both original source files match their exact members in
`ConZFC_Shared_Certificates_2026-10-24.zip`, SHA256
`61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1`.
All six physically copied entries of the seven-entry calibration pin
list match actual Git blobs at `08200eb10fde2db408c69dffd840d6920a569b1f`.
The uncopied entry is the unused expanded `affine_shared_step.json`
table; the operative source is fully supplied and independently bound
to Code254/KCode222. It is not a missing theorem hypothesis.

One harmless provenance normalization should be explicit: bundled
Mathlib `PellMatiyasevic.lean` has one extra final line feed compared
with declared Git blob `db9c757dd7cac29260397150fd190d72715ea3f8`.
Removing exactly that byte reproduces the blob hash. The recorded
SHA256 `4cb1a4f9fed854f7e3a340ff3810a60e07062447931063183b58180f376e4f38`
correctly authenticates the actual bundled bytes. No semantic source
change is involved.

After inspecting the executed scripts, I ran `verify_all.py` in normal
and optimized Python with bytecode writes disabled. Both reproduced all
nine defining artifacts byte for byte, checked 221 literal arithmetic
interfaces, rejected eight corruptions, and parsed all 491 printed
residuals plus 359 printed integer-guard indices. No Lean, TeX, inherited
H10 emitter, simulator, network or package installer ran. The original
archive and extracted source/artifacts remain unchanged.

`tools/review_shared_pell608.py` additionally executes no delivered
module: it authenticates the archive and manifest, source/Git bindings
and newline normalization, reconstructs both complete SOS polynomials,
and tests 46,441 exact factorial candidates, 46,417 strict ratio bounds
and 21 natural completeness witnesses, with all candidate outputs
through n=8 and boundary controls through n=20. Normal and optimized
runs pass. Their JSON receipts embed my fresh full-release replays.

The ordinary argument composes with the named C222/ZF/ZFC refutation
calibration. It supplies neither a new complete Lean theorem nor an
encoded object-ZFC proof. Consistency and absence of zeros are not proved.
