# Independent review: fully centered first-root carrier

**Verdict: pass.** The reviewed endpoint has 15 unrestricted integer variables,
exact total degree 48, and 108 live binary arithmetic operations (61
multiplications, 25 additions, 22 subtractions). Its zero set is in explicit
bijection with the retained fifteen-variable degree-56 predecessor. This review
checks the new ordinary arithmetic reduction, its literal transcription and its
inherited dependency boundary. It does not independently re-prove the unbounded
compiler/refutation theorem or prove consistency.

The companion `INDEPENDENT_CHECK.json` pins the reviewed equation, specification,
proof and TeX section. `independent_audit.py` imports neither builder nor the
producer's audit and never executes producer code. It accepts optional new and
predecessor directory arguments. Its default paths target this release layout.

## 1. Literal equation and accounting

All shared registers and three unchanged residuals agree with the retained
predecessor. The only new residual is

    Cnew = (Z + U k)^2 + 4 U (L Z - U)
         = Z^2 + 2(2L+k) U Z + U^2(k^2-4).

The final equation is the sum of the squares of Cnew and the unchanged strong,
auxiliary and guard residuals. This is a polynomial over the integers with no
extra quantified register, divisor, radical, inequality, or adjustable constant.

The independent checker parses the complete DAG, checks every node is a valid
causal binary addition/subtraction/multiplication or an allowed integer leaf,
traverses from the output, and counts the reachable operation nodes itself.
Every node, every one of the fifteen input variables and all six fixed numeral
ports are live. Counts are compared with, not taken from, producer metadata.
Thirty register-cut identities are compared with independently written expanded
expressions; the separate specification is checked against these same independent
mathematical expressions. All 108 single-live-gate opcode changes are rejected,
even after refreshing each mutation's operation-count metadata.

## 2. Unconditional divisions and all degenerate cases

The authentic fixed beta is 2^1064921-1, positive, odd and congruent to 1 modulo
3. For every integer j, q=beta(6j+1)+1 is even and congruent to 2 modulo 3;
therefore q is nonzero. H=4a+3 is odd and nonzero. Since a=(X+1)Y and Y=qv,
H is congruent to 3 modulo q. Consequently gcd(H,q)=1 and

    gcd(H,2q^2)=1; M=2q^2>0; U=MH is nonzero.

This argument permits negative q and negative H, and precedes use of any
residual. In particular the substitution t=Z/U is always legitimate over Q.

At a new zero, the sum of squares first gives Cnew=0. The rational t then obeys

    t^2 + 2(2L+k)t + k^2 - 4 = 0.

The rational-root theorem makes t an integer. From U dividing
Z=Un+M Klo+H(v-q^2), reduction modulo M and H and the proved coprimality give

    v0=(v-q^2)/M in Z, g=Klo/H in Z, t=n+g+v0.

No unproved cancellation occurs. In particular v=q^2(2v0+1) is nonzero: the v=0
branch is excluded at this stage, not omitted by a scale assumption. Reduction
of the monic equation modulo 2 gives t+k even. Equivalently the integer
x=t+2L+k satisfies x^2=4[1+L(L+k)], which forces x even.

There is no division by k, c, L, f, Q-1, a Pell radical, or a sum/difference of
radicals anywhere in this local reduction. Thus k=0, c=0, L=0, f=0, Q=1, and
vanishing radical-center possibilities do not require separate inverse maps;
all maps below remain valid whenever such an assignment is a zero. The full
polynomial in fact excludes k=0 because its guard budget is then nonpositive
while pos is at least one, but the local equivalence does not need this fact.
Negative roots and signs are retained. No positivity-based root choice is made.
If desired, writing L=ell*k with ell=XY^2 gives
Dtau=1+ell(ell+1)k^2>=1, but even this positivity is unnecessary for the maps.

## 3. Exact maps on every zero, not only canonical zeros

Write the old carrier as

    Cold(Z)=Z^2+(2Z-Uk)UL-U^2.

Direct expansion, independently checked symbolically, gives the universal
identity

    Cnew(2Z-Uk)=4 Cold(Z).

All other residuals and all shared registers before Z are independent of n.

From every new zero, set s=(t+k)/2, an integer by the parity argument, and
replace only n by

    nold=s-g-v0=(nnew-g-v0+k)/2.

Then Zold/U=s and Znew=2Zold-Uk. The identity makes Cold zero, and the other
three residuals remain zero. This produces an actual old integer zero.

From every old zero, its monic equation in sold=Zold/U makes sold integral.
The same CRT then supplies g and v0. Replace only n by

    nnew=2nold+g+v0-k.

Then Znew=2Zold-Uk, so Cnew=0 and the other three residuals remain zero.
Substitution shows these two n transformations are inverses. Thus the stronger
claim of a bijection of zero sets, with all other coordinates fixed, is valid.
The proof does not need an actual known zero, canonical witness selection,
additional index tuning, or any new Pell theorem.

The displayed maps are not claimed to be integral polynomial substitutions on
all ambient assignments: their divisions are justified on the zero sets, exactly
where the theorem uses them.

## 4. Exact degree and actual nonzero coefficient

Independent leading-homogeneous propagation at the literal DAG establishes
row degrees 24, 14, 18 and 16. For Cnew the unique degree-24 term is 4ULZ;
all its other expanded terms have degree at most 22. Since the degree-7 leading
part of Z is U0*n, it follows that

    (Cnew)24=4 U0^2 L0 n,
    P48=16 U0^4 L0^2 n^2.

Here q0=6 beta j, X0=12q0 w, Y0=q0 v,
U0=8q0^2 X0Y0, and L0=X0Y0^2(R0+hX0Y0).
Selecting h^2 yields the exact coefficient

    [j^26 w^8 v^10 h^2 n^2]P = 2^58 3^34 beta^26 > 0.

The exponent sum is 48. The other squared residuals have degrees at most 28,
36 and 32, so none contributes to this coefficient. Authentication of the
actual positive beta makes this an attained degree at the fixed constants,
not merely a generic or syntactic upper bound. The independent script verifies
both leading-form identities and coefficient extraction exactly.

## 5. Source provenance and theorem boundary

The six complete decompressed coefficient payloads are byte-identical to the
retained predecessor, match independently pinned SHA-256 values, have their
claimed bit lengths and canonical positive unsigned little-endian encodings,
and satisfy the actual beta/cone recipes. The MF convention is unchanged:
MF is already shifted by beta. The prior binding file is identical.

The predecessor equation, specification, proof, dependency document and source
pin file match its retained manifest. All five original mathematical source
files match their exact retained hashes. The new endpoint's five direct source
pins also resolve to these retained predecessor files. The semantic dependency
is solely the reviewed old15 equivalence to normalized17 and its stated native,
compiler and refutation chain. The local bijection introduces no new dependency
on the fourteen-, thirteen-, or twelve-variable sibling reductions.

The full predecessor archive/package and its own compiler/provenance material
must remain in the enclosing release. The new short proof plus coefficient
payloads alone would not constitute a standalone verification of the entire
consistency encoding. Neither this review nor the producer claims a new
end-to-end proof-assistant certificate, a new encoded object-language theorem,
absence of integer zeros, global optimality, or a proof of Con(ZFC).

## 6. Reproduction and scope

Run `python independent_audit.py` and `python -O independent_audit.py` from any
working directory, or provide the new and prior lowdegree directories as the
two positional arguments. The checker uses Python and SymPy and does not rely
on Python `assert`. Both normal and optimized receipts are retained here.

The 5,460 finite signed CRT diagnostics include negative q, negative H, and
v=0. They supplement, rather than replace, the universal proof above. Mutation
rejection checks transcription sensitivity, not logical completeness of an
unbounded theorem. The substantive ordinary proof and the literal finite
checks have been reviewed separately and agree.

## Final associative sharing review

The final graph reuses the already computed Y*k in L=E*(Y*k), rather than forming (E*Y)*k. This is the universal associativity identity and changes no register polynomial. The root reviewer reran this independently authored checker against the changed graph: all thirty exact register identities, leading forms, hashes, and108 live-opcode controls pass. Only the expected multiplication count and control total changed; the checker still derives all identities independently. Final normal and optimized receipts bind the actual108-gate graph.
