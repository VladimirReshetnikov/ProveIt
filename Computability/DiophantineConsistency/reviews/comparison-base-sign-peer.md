# Independent ordinary and literal review of the comparison-base lift

**PASS, scoped to the ordinary theorem and complete source-use ledger.**
I found no missing hypothesis or sign branch in
research/comparison-base-sign. The proof removes the raw657 guard by an
existential reconstruction; it does not assert that the original raw657
value is nonnegative. No 78-guard quartic or projected count is covered
by this peer. All frozen equations remain unchanged.

The exact reviewed note has SHA256
`c60a20bb5bf7e41f90fbe51df4953bbbe01106225fa1d0b301fd9ea874ba367c`.
The normal/optimized receipts pin its audit and closed packet, the entire
prior 79-guard packet, and the actual source bytes. Their independent
checker imports no author audit/checker/builder, optimizer or Pell
emitter. It replays the author audit only after the independent checks,
as a separate receipt-reproduction check.

## 1. Negative comparison bases preserve index recovery

The claimed extension keeps all original signed-index hypotheses,
including A>=2, natural x,Y,U,k with U>=2 and 1<=k<=Y, the three norms,
nonzero V with Y^2 dividing V, and the four congruences. Only B is
allowed to be an integer with abs(B)>=2.

Let b=abs(B) and e=sign(B), so e is exactly +1 or -1. Classifying the
positive-base norm solutions gives main index i, unit index n and
comparison index h, with independent signs on S and R. The old squared
divisibility argument gives i>0, n>0, i<=n and Y dividing n. It uses
only the A-based main/unit norms, so changing B's sign does not affect
any of these conclusions.

Since b=e*B and B=A modulo U, polynomial recurrence gives
chi_h(b)=e^h chi_h(A) modulo U. Combined with S=x modulo U and its
independent sign, this gives chi_h(A)=plus or minus chi_i(A) modulo
chi_n(A). The existing half-period sign change and residue
classification therefore give h=plus or minus i modulo 2n, including
the endpoint i=n. No division or residue cancellation is introduced.

Similarly b=e modulo 4Y. The same recurrence at +1 and -1 yields
psi_h(b)=e^(h-1)*h modulo 4Y for h>=1. The h=0 ordinate is zero and
cannot satisfy R=k modulo 4Y when 0<k<=Y. Thus its formally awkward
negative exponent is unnecessary. The independent sign of R absorbs
e^(h-1), giving h=plus or minus k modulo 4Y. As Y divides n, these
congruences imply i=plus or minus k modulo 2Y.

The old short interval 1<=i,k<=Y concludes i=k: the positive case has
i-k=0, while the negative case forces i+k=2Y and hence i=k=Y. This
explicitly includes Y=1 and i=n. The two parity factors are independent
signs, so no unstated relationship between S and R is required. The
proof does not require U odd or V positive in the abstract lemma.

## 2. Actual source excludes the small-base exceptions

The prior prefix proof, positive exponents and A>W^W bootstrap use no
raw657 sign. All Y>=k>=1, and the retained raw1214 product factor gives
V>0. The unit norm gives abs(U)>=A>=2. From the exact rows,

    B=1+4V(q4+1),    B-A=U*bq.

For q4>=0, B>=5. For q4<=-2, B<=-3. The sole remaining case q4=-1
would give B=1 and U dividing A-1, impossible because
0<A-1<abs(U). Therefore abs(B)>=3 before comparison classification.
The signed-B lemma applies at abs(U), x=abs(X) and
S0=sign(X)*S, with the original B left signed.

This restores exactly the missing B-positivity step of the 21-sign
proof. Its independently selected positive-base residue calls still
orient all original X values. The pow1 call at base92 still precedes
f0 positivity and the final raw753 modulus sign. No changed q4 or
comparison coordinate is used as an intended power value.

## 3. Existing U and V suffice for a simultaneous positive lift

Keep U signed and nonzero. With t=abs(q4)+1 define

    q4'=q4+abs(U)t,
    B'=B+4V abs(U)t,
    bq'=bq+4V sign(U)t.

The pointwise inequality q4'>=abs(q4)+2 follows from abs(U)>=2.
The constructor and congruence identities persist identically because
U sign(U)=abs(U). In particular B'>=5 and B'=A modulo U. There is
no new Pell-unit selection or CRT existence premise.

The already oriented main pair is X=chi_k(A),Y=psi_k(A). Choose
S'=chi_k(B'), R'=psi_k(B'). Polynomial base transfer gives
U dividing S'-X, and B'=1 modulo 4Y gives 4Y dividing R'-k. Both
denominators are nonzero. Thus the fresh progression quotients are
integers even when U<0. They need not be nonnegative. Their norm is
exact. The same one B' works for all 15 seeds; no coprimality among
the Y values is assumed.

The only additional guard subsequently needed is a new Legendre
triple for the new positive q4'. The other 78 guard values and their
existing triples are literally fixed. Forgetting that triple proves
the reverse existence direction. There is no claimed inverse of this
existential reconstruction and no pointwise all-natural claim.

## 4. Full literal reconstruction boundary

The peer reconstructs the gate inventory directly from the original
1177 source rows, checking all 1029 unique unit pivots and strictly
earlier operands. The complement contains all 148 nongate rows. It
then computes dependencies over this complete inventory, including
constraints outside the supplied private-row list.

Exactly 62 free coordinates change: q4,bq and S,R,Squotient,Rquotient
for each of the 15 seeds. Their closure contains exactly 141 gates.
Exactly 46 of all 148 nongate constraints are affected: the 15
comparison norms, 30 progressions and B_mod_U. For every affected
constraint the peer independently specifies the intended polynomial,
recollects the full original-row ideal, and verifies that its sole
nongate term is that constraint with coefficient 1. Consequently
restoring the unit gate equations and satisfying the intended
polynomial forces the actual constraint to vanish, without division.

All 78 retained guards, all 643 prefix coordinates, both common-unit
values, the discriminant/bootstrap/frame, all 16 main pairs (including
the derived pair), all 21 actual power arguments and their quotients
are outside the closure. Every other source row is therefore either
unchanged or restored by an exact topological gate definition. This
checks the entire source, rather than only a named macro boundary.

The peer rejects six corruptions, including a q4 use hidden in a
semantic nongate row outside the private inventory. It collects both
universal lift identities. Independent finite diagnostics cover 90
negative-base parity cases, 416 base +/-1 congruences, 434 positive-q4
bounds with either U sign, and explicit negative-B endpoints
A=3,U=+/-3,V=1,B=-3,X=3,Y=k=1 (so i=n). These controls accompany the
unbounded argument; they do not prove it by sampling.

Both modes reproduce the complete author receipts. Commands:

```sh
python -B Computability/DiophantineConsistency/reviews/comparison-base-sign-peer.py --output /tmp/comparison-base-sign-peer.json
python -B -O Computability/DiophantineConsistency/reviews/comparison-base-sign-peer.py --output /tmp/comparison-base-sign-peer-optimized.json
```

The ordinary consistency/source dependencies and their internal-ZFC
status are inherited unchanged. A full new 78-guard equation and all
projected coefficient/domain certificates remain a separate step,
requiring root acceptance before materialization.
