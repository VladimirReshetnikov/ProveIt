# Identification of the calibrated syntax

The literal parent and this release use the square-shell `xx0` recoding of
C222, not the original Cantor arithmetic constructors. The existing
ordinary recoding theorem is supplied unmodified as
`inherited/shell_recoding_supplement/SHELL_ENCODING_PROOF.md`, with full
source provenance next to it. This note identifies the exact composition;
it does not claim a new recoding theorem or a new compiled formal proof.

For s=x+y, set Q0=s^2+x and Q1=s^2+3x+4y+3. The ranges of Q0 on a fixed
shell are [s^2,s^2+s]. The ranges of Q1 on the preceding shell x+y=s-1
are [s^2+s+1,(s+1)^2-1]. They are disjoint, cover the natural numbers,
and each has an explicit inverse. Parity splits these two maps into the
four constructors I=2Q0, M=2Q0+1, A=2Q1, E=2Q1+1.

Every positive constructor value strictly exceeds its arguments. The only
exception to recursive descent is I(0,0)=0, shared by both coding schemes
and treated as the distinguished zero base case. Define f(0)=0; for n>0,
decode n uniquely as an old Cantor constructor C_old(x,y) and set
f(n)=C_shell(f(x),f(y)). Define the inverse g similarly. Course-of-values
induction proves totality, the constructor identities, and that f and g
are inverse. They fix 1 as well as 0 and preserve equality and disequality.

The consequence needed by the release is

    finite shell-C222 derivation of 1
      iff finite Cantor-C222 derivation of 1.

Truth, modus ponens, generalization, and all unguarded axiom schemata
transport by the constructor identities. The guarded bundle transports
because its two freshness disequalities are preserved by the bijection.
At the arithmetic source layer the guard is

    ((c-a)(c-b))^2=(d+1)^2,  d>=0.

For a transported bundle instance use

    d_new=abs((f(c)-f(a))*(f(c)-f(b)))-1.

It is nonnegative precisely because both transported differences are
nonzero. The inverse uses g. The separate logical schema in which d is an
ordinary code parameter instead transports that parameter by f. These
are alternative local rule branches, so there is no requirement to assign
the two distinct witnesses simultaneously to one chosen rule instance.

After this recoding step, the retained named interfaces
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` give the remaining
logical calibration. Therefore the complete semantic chain for the new
polynomial is

    integer zero
      iff finite shell-C222 refutation
      iff finite original C222 refutation
      iff finite ZF refutation
      iff finite ZFC refutation.

All mappings are finite recursive syntactic constructions. The inherited
proof supplies their ordinary ZFC formalizability. The numerical sizes of
codes are not preserved by f; the arithmetic circuit uses the actual shell
constructors and their own inherited majorant certificates. In particular,
one must not substitute the earlier Cantor formula for I into the literal
polynomial or use an old numerical size bound without the shell ledger.


