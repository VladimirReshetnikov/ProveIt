# First full ordinary review: the main-trace fold obstruction

**PASS_LOCAL_ORDINARY_OBSTRUCTION_ONLY; no finding or requested correction.**
Reviewer `/root/intake_e13` authored neither this source nor the failed lead and
is not ROOT, who contributed the missing-step finding. This is the FIRST full
independent review of the exact three-file r1 source at actual commit
`46482466358824b9f998287623d76c009931dbf7`, manifest
`793ec98774fb20064c9f38c2edc70adac4877662ee5495e0071a506c5c77cd6e`.

I read all138 README,26 SOURCE_PINS.json and17 manifest lines; freshly read the
165-line normalized auxiliary-index lemma,260-line normalized67 proof and138-line
4027 TeX. All four directly pinned contracts authenticate. The547-line native
proof is hash-authenticated context, not freshly full-read; it is not needed to
prove this local arithmetic obstruction. No transitive native/Lean audit is
claimed. The auxiliary lemma's pins were read to locate its mathematical scope,
not to adopt its entire transitive closure as independently authenticated here.

## Exact signed-fold endpoint

Assume the local INTEGER norm hypotheses in the source. Write Delta=A²-1.
Main Pell classification gives D=chi_A(m),c=psi_A(m),m>=2 and D>2c.
Auxiliary classification retains e=sign(V), with an odd positive index n=2j+1:
V=e Q_j(S²). Even indices cannot give S|chi_S(n); V,y are nonzero.

The three Q identities follow from the odd-subsequence recurrence. In particular
S²=Delta(D²-1) is1-A² modulo D, and the literal V gives V=-c modulo D.
Thus psi_A(n)=±c modulo D. The doubling matrix is -1 after2m modulo D,
so folding n to r in[0,m] preserves psi up to sign. Since psi_A(r)<=c<D/2,
the only possible residue is psi_A(r)=c, forcing r=m, not r<m. Therefore
n=(2t+1)m with t>=0, and n odd forces m odd. Keeping the sign of V gives
-R=e(-1)^j n modulo c. The removed strong equation is exactly what formerly
gave c|m; the main norm gives no such divisibility. The old strict fold endpoint
was excluded because its strong ordinate ic² exceeds c. This is the correct
comparison with the full165-line lemma, not an accidental reuse of that lemma
under weakened hypotheses.

## Every odd multiple survives the squared modulus

For odd k, composition gives psi_A(km)=c psi_D(k). The odd subsequence of
psi_D has constant terms1,-1,1,... modulo D², so
psi_D(k)=(-1)^((k-1)/2) modulo D². Also S²=1-A² modulo D². Consequently
Q_((km-1)/2)(S²)=(-1)^((km-1)/2+(k-1)/2)c modulo D².
For m=3 modulo4 the exponent is k(m+1)/2-1, always odd. Hence the negative
residue -c holds for EVERY positive odd k. Neither the mod-D fold nor the
stronger literal mod-D² residue selects k=1. No sign was silently discarded.

## Complete strictly positive local witness

Hand calculation gives psi_4(3)=4*4²-1=63,chi_4(3)=4*4³-3*4=244,
Delta=15 and S=945. The main norm is244²-15*63²=1. Take k=5,n=15,R=15,
V=chi_945(15)/945=Q_7(945²),y=psi_945(15). The odd quotient identity makes
V an integer; both V,y are positive, and its Pell norm is exactly
S²(V²-y²)+y²=1. No huge coordinate was expanded or numerically evaluated.

The explicit psi_D(5)=16D⁴-12D²+1 is1 modulo D²; therefore
V=-psi_4(15)=-c modulo D². Independently S=0 modulo c gives V=-15=-R
modulo c. With D²=1 modulo c and gcd(c,D)=1, the numerator
V+c+R D² is divisible by BOTH coprime c and D². Thus
T=(V+c+R D²)/(cD²) is a positive integer and rearranges to the EXACT
literal V=D²(cT-R)-c. Finally0<15<63/2, but15 is not3, and strict Pell
growth gives psi_4(15)>psi_4(3)=c. This disproves the proposed LOCAL implication
to c=psi_A(R), including its index window and both literal norm congruences.

It is NOT a whole13-variable zero: there is no supplied first norm, actual
front/rank/mask/transport/native tuple or refutation. In particular local A4/R15
are not alleged to satisfy the much larger actual q/front/rank constraints.
Additional outer information might exclude this local family or support a
new argument. No claim that the full failed candidate has false zeros follows.
The tentative61/139 count/degree and13-variable consistency endpoint are unaccepted.

## The distinct old-i=1 obstruction

Keeping the OLD c² strong ordinate with i=1 requires f²=1+Delta c⁴.
The main norm makes this(cD)²-c²+1. It is below(cD)² by c²-1>0 and above
(cD-1)² by c(2D-c)>0. Hence no integer f exists. This rejects exactly that
constant-multiplier shortcut, not every possible replacement norm or encoding.
The actual versus normalized P66 strong factor remains distinguished: only
the normalized factor is1; the old unscaled factor is Delta when it holds.

## Preservation, arithmetic scope and verdict

The source wording “no numerical Pell sequence was evaluated” is read honestly
as no program/no expansion of the large auxiliary pair. The small c,D,S values
are explicitly HAND calculated above and in the source. I used only hand
algebra and inert text/JSON/hash/Git readers/writers: no Pell/residue/sequence
helper, application, import, AST, compiler, Lean, TeX/PDF, tuple or search ran.

Whole r1 member names/bytes and actual Git blobs authenticate. The earlier
5787-byte README is byte-identical and its0-byte pins remain preserved; the r1
metadata does not overwrite that ENOSPC first write. The cause/history is a
credited ROOT/author observation, not an independently witnessed app failure.
All nine recorded source/history files remain exact before and after this review.
No source, parent, main, held artifact or earlier review was modified; no commit.

The precise accepted review scope is the local obstruction and its proof.
No maintained equation change, global lower bound, finite endpoint, page result,
new native theorem or runtime authority is established. ROOT's separate ordinary
disposition remains its own action; this reviewer supplies no author repair.
