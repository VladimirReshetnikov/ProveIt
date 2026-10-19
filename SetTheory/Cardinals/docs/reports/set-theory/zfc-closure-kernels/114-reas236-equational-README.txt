E639 SUPPLEMENTARY EQUATIONAL CONSISTENCY RESEARCH

Final research packet: E639, 639 logical bits, seven equations, nine
operations, four local variables, 144 equation-term nodes, query Q(d)=d.
Its transport file has 80 bytes with one padding bit. A protected false
class in the parameter tail allows the descriptor itself to be the code,
saving the three V(b,d) projections. self_descriptor.tex gives the full
ordinary relative model proof. This is separate from the binary TM work.

  python3 -B build_e639.py --output /tmp/e639-replay

Checkpoints: E668 has the new descriptor with the old truth equation/query;
E643 deletes the redundant truth equation; E639 shortens the query. The
script also preserves the independent E667/E663 line below. The compared
input is exact E692 from pinned ProveIt, not an assumed E688 input.

E667/E663: SAME EQUATIONAL THEORY AS THE PINNED E692 PACKET

Result: 667 logical bits, seven equations, nine operations, four local
variables, 150 equation-term nodes, and the same query N(d,d)=d.
The transport file contains 84 bytes and five trailing zero padding bits.
This is an equational presentation, not a binary Turing machine.

The exact new contribution is the deletion of E692 equation 1,
d=N(d,N(d,d)). It is derivable from retained Sh1, the native head equation,
the class NAND equation, and the final mux closure equation. Theorem and
full formulas: top_elimination.tex. The proof is a finite algebraic one,
requires no ultrafilter, and does not use the intended EPSC interpretation.

Run with Python 3.10 or later:
  python3 -B build_e667.py --output /tmp/e667-replay

The script identifies the input bytes, reproduces E692's original bits,
deletes just one equation, checks the retained proof premises, verifies the
new Boolean identity by exact Boolean-ring normalization, and round-trips
the resulting packet through a separately implemented strict decoder.
It writes equations, JSON syntax, .bits, .bin, .bitlength, and a receipt.

Primary algebra source: McCune, Veroff, Fitelson, Harris, Feist, and Wos,
Short Single Axioms for Boolean Algebra, JAR 29 (2002), Theorem 2 (Sh1).
  https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf
  https://www.cs.unm.edu/~mccune/papers/basax/Sh-1.proof
  https://doi.org/10.1023/A:1020542009983

Inherited input: ProveIt commit
1b27f052d770f4c7d435e82e779bf21f5a1f66ed, archive
docs/incoming/ZFC_Sub237_Research_2026-10-19.zip, member
zfc_sub237_research_20261019/equational/generated/E692.json.
The original input attribution and license are kept under inputs/.
Its raw EPSC/E713/ZFC calibration is inherited, not re-proved here.

New source was written for the 19 October 2026 sub-237 research session.
The E692 formula terms, signature order, query, and packet conventions
retain their original attribution. No priority claim beyond this concrete
new deletion against the inspected packet is made.

Prior contribution: Source104 deleted the same explicit truth axiom from
E946 to get E921, using its old arbitrary-witness equation. That equation
is absent from E692's complemented-binder interface. Our distinct proof
uses the retained final closure and head rows. The general truth-deletion
idea is credited to Source104, not claimed as a first discovery here.
