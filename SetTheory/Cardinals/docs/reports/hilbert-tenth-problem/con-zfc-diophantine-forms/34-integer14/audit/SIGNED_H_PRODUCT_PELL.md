# Removing the Jones j-positivity guard by signed index reflection

Let A,B,C,J be positive integers with A>1, B>1, B<=C, J>0,
and assume 2B<=C or B is odd. Let i be any nonzero integer and j any
integer. Define

D=(A^2-1)C^2+1, E=i J D C^2, F=(A^2-1)E^2+1,
G=A+F(CD+1-A), H=B+jC, I=(G^2-1)H^2+1.

Suppose DFI is an integer square and F divides H-C. Then
C=psi_A(B), where psi_A is the Pell sine sequence with recurrence
psi_A(n+2)=2A psi_A(n+1)-psi_A(n), psi_A(0)=0, psi_A(1)=1.

## Proof

Replacing i by |i| leaves D,F,G,H,I unchanged. Thus E may be assumed
positive. The standard product-Pell argument gives D,F,I positive,
G>1, and pairwise coprime D,F,I. Indeed F=1 modulo D, G=1 modulo D,
I=1 modulo D, G=A modulo F, and H=C modulo F imply I=D modulo F.
Hence all three factors are positive squares.

The Pell parametrization supplies nonnegative indices t0,t1,t2 with
C=psi_A(t0), E=psi_A(t1), |H|=psi_G(t2). As in the pinned
ProductPell proof, C^2|E implies C|t1; also t1>=2, 1<=t0<=t1,
and F=chi_A(t1)^2. Set k=chi_A(t1)>0.

If H>=0, the original proof applies verbatim: H=psi_G(t2),
psi_A(t2)=C modulo k, and t2=B modulo C. The usual Pell
index-congruence lemma gives B=t0 or B=-t0 modulo C, and the
productPell_index lemma gives C=psi_A(B).

If H<0, then psi_A(t2)=-C modulo k. Let
M=[[2A,-1],[1,0]]. The determinant of M is1 and the trace of M^t1
is2chi_A(t1)=0 modulo k. Cayley-Hamilton therefore gives
M^(2t1)=-Id modulo k, and M^(4t1)=Id modulo k. Choose a positive
integer Q large enough that n=4t1 Q-t2>=0. The inverse-matrix
identity for the Pell sine coordinate gives

    psi_A(n)=-psi_A(t2)=C modulo k.

Since G=1 modulo C, psi_G(t2)=t2 modulo C. Thus H=-psi_G(t2)
implies -t2=B modulo C. As C|t1, the reflected index satisfies
n=-t2=B modulo C. Apply the same ordinary index-congruence lemma
now to n in place of t2. Its conclusions are n=t0 or n=-t0
modulo C, so again B=t0 or B=-t0 modulo C, and the unchanged
productPell_index conclusion follows. This proof does not require
j>=0 or H>=0. The case H=0 causes no issue for the nonnegative
branch; alternatively F>C and F|H-C exclude it.

## Application to the Jones ratio conditions

Retain the guards on g,s,w,phi and the positivity consequence for h.
They imply R>0,A>1,C>=B=2R+1>1, with B odd. Keep i!=0 but drop
the guard j0>=0: put j=j0+1 with j0 an arbitrary integer.
From JF|QF+J(H-C) and gcd(J,F)=1, derive J|Q and F|H-C.
The signed-H lemma yields C=psi_A(B). The standard constructive
product-Pell theorem then supplies fresh positive i',j' for these
same A,B,C,J. Their F',H' satisfy F'|H'-C. Together with J|Q this
restores JF'|QF'+J(H'-C), and D F' I' is square. The radicand a0
and margin m do not depend on i,j, so they remain unchanged.
Thus any signed-j ratio solution can be replaced by a genuine
positive-j ratio solution. Completeness is immediate because the
original positive witnesses are still allowed.

This removes one guard witness from the coprime Pell stack. It uses
ordinary Pell theory and matrix arithmetic, not a newly compiled
formal theorem. The exact source proof inspected is
Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean,
psi_of_ProductPellConds and productPell_index, at commit
8c6eec9d19ef80538c8e61ff6e0180040583446a.
