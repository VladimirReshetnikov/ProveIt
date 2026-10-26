# Independent review of simultaneous orientation and power pooling

Prepared within the AI-assisted workflow, 25 October 2026. This is an
ordinary mathematical and literal-interface audit, not an external human
review or a new proof-assistant certificate.

## Result

The proposed fusion is valid. It may remove the parent orientation
quotient x201 and its sole row142 in addition to the ten coordinates and
ten rows removed by P207. The canonical-index premise needed by P207
must be replaced by a weaker **raw Pell index bound**, proved from the
retained cap before orientation. That weaker premise is available in
the actual P216 source, and the independent port audit now checks its
literal equations and dependency order.

The resulting equation has206 unrestricted integer coordinates and143
residuals:142 quadratic residuals and the single degree-at-most13 fused
residual. Thus the full sum-of-squares polynomial has degree at most26.
The stated degree26 is exact once the same nonzero degree12 power-pool
leader is multiplied by the affine factor A-1; no orientation term can
cancel it because that part has degree at most12. The literal artifact
has a separate exact checker and receipt when emitted.

## 1. The needed raw index bound is available before row142

I read the signed-anchor argument in repository report135,
`direct/ORIENTATION_FIRST_PROOF.md`, especially the section titled
"A signed nominal index in the squared anchor". It proves the absolute
anchor index is |h| before applying the pooled orientation congruence.
It then bounds every other actual classified Pell index below |h|.
The proof does not assume h>0 or positive arithmetic representatives.

The source has changed since report135, so that textual statement alone
is insufficient. The updated independent `../code/audit_parent_ports.py` reconstructs
the actual current cap and all auxiliary/comparison rows from P216. In
the current coordinates the anchor ordinate is C=x184, its nominal index
is the restored affine polynomial J, and its abscissa is x183+x185.
The exact strict cap is

    C²=1+J²+Σ_(13 nonanchor pairs) Y_i²
          +u²+v²+w(w+1).

For unrestricted integers all three slack terms are nonnegative.
Therefore C is nonzero, |C|>|J|, and every other |Y_i|<|C|.

The auxiliary ordinate is an odd multiple of C². Its norm and the
anchor norm classify their absolute indices i,l at |A|, with
|C|=Y_i(|A|), and the squared-ordinate divisibility lemma gives |C||l.
The retained comparison base is1 modulo4C and is congruent to A modulo
the auxiliary abscissa. The comparison abscissa agrees with the anchor
abscissa modulo that same modulus; its ordinate agrees with J modulo4C.
The signed trace-residue lemma consequently gives

    i=+J or -J modulo2|C|.

Since1<=i<=|C| and |J|<|C|, J=0 is impossible and i=|J|. This is the
same signed-anchor implication as the inherited theorem. It uses no
power certificate or orientation quotient. The strict cap gives
j_i<|J| for every other raw classified index.

The independently recovered square frame contains J² and gives J²<W.
Thus all actual raw indices satisfy j_i<=b=floor(sqrt(W-1)). This is
stronger than merely j_i<W and is precisely the bound required by the
fusion estimate.

All14 raw cap/anchor/large-center identities are checked in the updated
`../verification/P216_PORTS_AUDIT.json`. Their final-row combinations avoid row142 and
every removed power row. The coordinate x201 occurs only in row142.
The large-A bound also follows independently from rows92--94 as
explained in the P207 review.

## 2. Classify raw pairs without assuming orientation

For a raw norm solution at signed parameter A, write

    X_i=epsilon_i X_(nu_i)(A),
    Y_i=epsilon_i Y_(nu_i)(A),
    epsilon_i in{-1,1}, |nu_i|<=b.

This notation covers the two independent coordinate signs: choose
epsilon_i to match the abscissa relative to the signed-center Pell
polynomial, and choose the sign of nu_i for the ordinate. At index0,
the ordinate is zero and either abscissa sign is still covered.
The relation remains valid when A<0; the recurrence polynomials already
include their parity-dependent center signs.

Put D=A-1 and

    Omega=Σ_i[(X_i-1)²+(Y_i-k_i)²].

Reduction modulo D gives

    Omega = O mod D,
    O=Σ_i[(epsilon_i-1)²+(epsilon_i nu_i-k_i)²].

This follows from X_n(A)=1 and Y_n(A)=n modulo A-1 for every signed
integer n. It does not assume that nu_i is the requested index k_i.
The representative O is nonnegative and bounded by14(4+4b²).

At a nonzero base n_j, the power-evaluation residue is now

    X_i+(n_j-A)Y_i=epsilon_i n_j^(nu_i) mod T_j.

This is the correct raw-pair congruence before orientation; using n_j^k_i
at this stage would be circular.

## 3. Fused integer equation and soundness

Let T_j=2An_j-n_j²-1 and E_j be the same residual blocks as in P207.
Let Pi=product(T_j), over all five blocks. The new polynomial residual is

    Omega*Pi + D*Σ_j n_j E_j product_(l!=j)(T_l) - z*D*Pi.

All T_j and D are nonzero before power interpretation. Dividing by
D*Pi says

    Omega/D + Σ_j n_j E_j/T_j is an integer.

Use the same nonzero-base clearing product C0=product(n_j^b).
For each nonzero block set

    d_i=C0*m_i-epsilon_i*(C0/n_j^b)*n_j^(b+nu_i).

Then C0*delta_i=d_i modulo T_j. Multiplying the preceding integral
rational sum by C0², subtracting the integer Pell-norm correction and
replacing numerators by congruent small representatives gives

    V=C0²*O/D+Σ_j n_j Σ_i d_i²/T_j in Z.

Every term is zero or has sign sign(A): D and A have the same sign,
and n_j/T_j has that sign for each nonzero base. The zero-base terms
are identically zero. Hence there is no cancellation among errors.

With at most5 blocks,17 power requests and14 raw pairs, the total
absolute small numerator is bounded by

    C0²*14(4+4b²)+Σ_j |n_j|Σ_i d_i²
      <188 b^(12b+2)<W^(6b+2)<=W^W.

The first bound is deliberately conservative. The second uses188<W,
b²<W and b>=16. For the denominators, |T_j|>W^W at nonzero bases,
while |D|>=W^W follows from the integral inequality |A|>W^W.
Thus |V|<1 and V=0. Same-sign terms imply O=0 and every d_i=0.

Consequently every epsilon_i=1 and every nu_i=k_i. All raw pairs are
now canonically oriented at their requested signed indices, and all
nonzero-base power requests are exact. This supplies both conclusions
simultaneously, in an acyclic order. The retained arithmetic bootstrap
then rules out the zero bases exactly as in the verified P207 proof.

## 4. Completeness and restoring the parent

For a genuine parent zero, Omega/D is its old integral orientation
quotient, and each E_j/T_j is integral. Their weighted sum supplies z.

Conversely the preceding argument restores canonical pairs and all
nonzero-base powers, followed by the same arithmetic bootstrap making
every base nonzero. The original ten power coordinates are restored as
in P207. Set the old orientation quotient x201=Omega/D, an integer
because canonical Pell coordinates have X_i-1 and Y_i-k_i divisible
by D. The literal row142 differs from Omega-D*x201 only by retained
frame and norm rows, whose exact combinations are in the port audit.
Thus row142 is restored too. This proves existential zero-set equivalence
with the authenticated P216 parent, without claiming a polynomial
bijection on arbitrary tuples.

## Proof boundary

The new small-integer fusion argument is fully given above. The
classification of Pell solutions, squared-ordinate divisor theorem and
signed trace-residue theorem used in the anchor argument are the stated
inherited ordinary dependencies, read in the original source chain.
The exact current cap and residue hypotheses were checked afresh.
No finite test replaces these unbounded theorems. The C222/ZF/ZFC
refutation interpretation is inherited unchanged; composing it proves
the requested equivalence in ZFC, without deciding consistency.
