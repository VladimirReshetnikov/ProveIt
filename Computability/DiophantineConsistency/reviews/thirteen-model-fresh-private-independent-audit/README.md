# Independent conditional fresh-private audit

The read-only audit of committed packet `6e71b6c877` actually exited 0 in
session 31945. The [receipt](CHECK.json) is bound by the
[terminal observation](terminal-observation.json). The script checks the
committed packet bytes, the author's outer session 72170 and its recorded exit
0, the two compiler and two dependency-check exits on each side, source and
object hashes, all 74 project links per side, BusyBeaver links, direct imports,
and pinned Lean and parent-audit inputs. It independently reran both prior
read-only parent audits and compared their output to their pinned receipts.
It did not run Lean. Parent artifacts reside in `/tmp`; availability of that
tree is required for replay. Matching sibling hashes and these checks do not
independently establish package-transitive or dynamic provenance, nor the
unobserved Foundation wrapper exit.

Both sides contain the same two compiled objects. Each carrier compilation
reported three `push_neg` deprecation warnings; the assembly compilations had
none. All four reported only Lean metatheory axioms `propext`,
`Classical.choice`, and `Quot.sound`, with no recorded `sorryAx` or errors.
These are not a statement that those axioms belong to object-theory iPRA.

The generic carrier theorem assumes an IΣ₁ model, I≥2, u,y,b,G positive,
b∣G, 4b∣y+1, and I²u²+y²=1+I²y². It obtains positive m with
−ιy=1+4(ιb(ιm−(ιu)²ιG)−ιG). The assembled theorem assumes arbitrary model
naturals a,R,b,G with b>0, R mod 4=3, G>0, and b∣G. It defines
c=ycoord(R,a), constructs positive f,i,T,u,y,m, sets
I=delta(a)·b·i·c², and proves the strong and auxiliary norms, ordinate and
abscissa equations, two residue conditions, T equation, and the displayed
signed carrier equation. In particular, positivity and b-divisibility of G
are supplied, not derived from a graph zero.

The author records an earlier exploratory parser failure in session 87465,
with `sorryAx` printed for the incomplete theorem; the corrected exploratory
session 37672 is recorded as exit 0. These exploratory terminal transcripts
are not retained in this packet and were not independently re-observed here;
they are not evidence for the final paired result. The paired successful
compiler output is retained in the pinned receipt and was checked separately.

This is a conditional model lemma. It does not establish the 69-operation
graph converse, literal graph binding, fixed-port calibration, a closed
internal derivation, or an iPRA equivalence.
