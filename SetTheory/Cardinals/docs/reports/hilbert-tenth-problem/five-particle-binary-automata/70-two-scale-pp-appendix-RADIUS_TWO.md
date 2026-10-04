# Separate bounded appendix: binary reversible radius-two classification

Status: complete finite certificate with two independently written exact-algebra checks. No external novelty claim. This is not used in the two-scale recognition proof.

## Statement

A one-dimensional binary CA with neighborhood contained in[-2,2] that is number-conserving on finite configurations and injective on the full binary shift is one of the five coordinate projections

    f(x_-2,x_-1,x_0,x_1,x_2)=x_j, j in{-2,-1,0,1,2}.

Thus any computationally universal binary full-shift-reversible number-conserving CA in this standard symmetric-radius convention has radius at least3. This conclusion does not apply to partitioned, time-dependent, second-order, nonuniform, or larger-alphabet models.

## Completeness argument

The Hattori–Takesue/Boccara–Fuks identity, displayed as Theorem1 in Fuks–Sullivan(2007), determines an n-input conservative rule from its values on words with first symbol0:

    f(x1,...,xn)=x1+sum(k=1,...,n-1)[
      f(0^k,x2,...,x_(n-k+1))-f(0^k,x1,...,x_(n-k))].

Here n=5 and f(00000)=0. There are exactly2^15 assignments to the remaining leading-zero outputs. Substituting every assignment into the identity, retaining precisely the Boolean output tables, gives428 distinct rules. This is the known conservative-rule count, independently recovered here.

For each of423 nonprojection tables the JSON certificate gives two distinct words of length4,5,or6 with identical one-step cyclic output. Repeating each word bi-infinitely gives two distinct full-shift inputs with the same image, proving noninjectivity. There are164 first witnessed at length4,179 at length5, and80 at length6. This is a finite collision proof, not an inference that long random trajectories look irreversible. The five remaining rules are explicitly projections, hence shifts and bijective.

The producer implements the leading-zero identity. The independent verifier enumerates from trailing-zero outputs using the spatially reversed identity, builds the full table set separately, and directly validates each collision bit by bit. It imports no producer or external scientific code. Its final assertion says that the423 certified tables and five projection tables are disjoint and cover the independently enumerated428 tables.

## Reproducibility and files

- radius2_algebra.py: freshly authored inspected finite Boolean algebra, writes certificate and prints count receipt
- radius2_certificate.json:423 explicit rule-table collisions, plus five projections
- verify_radius2_algebra.py: separate reversed-identity completeness enumeration and direct collision verification
- radius2-enumeration-receipt.json and radius2-verification-receipt.txt: observed successful executions

These programs compute only static local tables and one-step finite maps. They execute no archive code, external scientific interpreter, stored schedule, Lean, or multi-step trajectory simulator. Their relative certificate paths make the appendix relocatable.

## Primary literature and priority limits

Fuks and Sullivan, *Enumeration of number-conserving cellular automata rules with two inputs* (2007), Theorem1 and Section2, give the identity and record the binary n-input counts1,2,5,22,428. https://arxiv.org/pdf/0711.1349

Wolnik and De Baets, *All binary number-conserving cellular automata based on adjacent cells are intrinsically one-dimensional* (2019), establish the adjacent-cell classification. In one dimension the conservative radius-one possibilities are identity, both shifts, and both traffic rules; the traffic rules are not reversible. https://journals.aps.org/pre/abstract/10.1103/PhysRevE.100.022126

Morita, *Universality of One-Dimensional Reversible and Number-Conserving Cellular Automata* (2012), constructs a96-state four-neighbor RNCCA and discusses earlier small-state/small-neighborhood RNCCA decomposition experiments by Schranko and de Oliveira. The96-state result does not supply a binary five-particle radius bound. Its introduction is a reason to check that earlier paper before claiming originality for radius-two classification. https://arxiv.org/pdf/1208.2760

The earlier paper is Schranko and de Oliveira, *Derivation and representation of one-dimensional, reversible, number-conserving cellular automata rules*, Journal of Cellular Automata6(1):77–89 (2011). Its authors' publication list verifies the bibliographic entry, but its full text was not obtained in this bounded search. Therefore this packet claims an independently certified project appendix, NOT a new literature theorem. https://professor.mackenzie.br/pedrob/RESEARCH/PAPERS/publications-Themes.html
