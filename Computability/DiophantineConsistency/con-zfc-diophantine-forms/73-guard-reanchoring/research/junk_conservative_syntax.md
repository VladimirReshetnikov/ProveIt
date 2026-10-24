# Injective arithmetic syntax with harmless extra constants

Research note, 23 October 2026. This proves a generic compiler lemma; it does not claim a new closed Con(ZFC) polynomial or a frontier improvement.

## Arithmetic constructors

Let J(a,b)=(a+b)^2+a+1 for a,b in N. Use the two constants e=0 and i=1, binary constructors U(a,b)=4J(a,b), C(a,b)=4J(a,b)+1, and unary constructors N(a)=4a+2, V(a)=4a+3.

J is injective. Writing s=a+b, J lies in [s^2+1,s^2+s+1]; these intervals are disjoint because (s+1)^2+1>s^2+s+1. Once s and J are known, a=J-s^2-1 and b=s-a. Also J(a,b)>max(a,b). The four constructor ranges and the two designated constants are disjoint, and each child code is less than its parent code.

For every natural n define a finite term delta(n) by strong recursion. Decode constructor values in their unique way; decode 0 and 1 as the two designated constants. Every remaining n decodes as a new constant kappa_n. The recursion terminates and delta(U(a,b))=U(delta(a),delta(b)), with analogous statements for all constructors.

## Conservativity theorem

Let E be a finite or recursively given collection of equational axiom schemata in this signature, and let s=t be a closed original-signature equation. Encode axiom instances and equational proof steps by the displayed arithmetic constructors; allow arbitrary natural values for all term-code variables. There exists such an arithmetic proof of the encoded s=t if and only if E derives s=t in the original signature.

Forward proof: decode every natural term code using delta. Each arithmetic step is a legitimate equational step in the signature enlarged by the kappa_n. Replace all kappa_n simultaneously by the original constant e. This syntactic homomorphism fixes s,t, sends each E-instance to an E-instance and preserves every inference rule. Thus it gives an original-signature proof of s=t. Reverse proof: encode an ordinary finite equational proof using the displayed constructors. No semantic soundness or consistency premise is used.

Consequently a front end for a finite equiconsistent equational theory does not need to check whether an arithmetic term code belongs to the image of the original term encoding. A bijective numbering is convenient but unnecessary. This differs from treating ill-formed codes as unconstrained assertions: only terms have extra constants; each equation and inference is still explicitly checked.

## Explicit local inference polynomial

An equation is represented by its two term codes. Let (a,b) be the conclusion, (c,d) the first premise, and (e,f) the second. Let z be one natural auxiliary variable and define

R=(a-b)^2,
T=(c-e)^2+(a-d)^2+(b-f)^2,
B=(a-4J(c,e)-z)^2+(b-4J(d,f)-z)^2,
W=(a-4c-2-z)^2+(b-4d-2-z)^2,
I=z^2(z-1)^2+R*T*B*W.

All factors are nonnegative. Hence I=0 if and only if z is 0 or 1 and at least one of these valid equational steps holds:

* reflexivity a=b;
* from c=d and e=f with c=e conclude d=f (Euclidean transitivity);
* congruence of U (z=0) or C (z=1) using both premises;
* congruence of N (z=0) or V (z=1) using the first premise.

The Euclidean-transitivity rule plus reflexivity derives symmetry and ordinary transitivity. These rules therefore generate ordinary equational consequence when supplemented with the selected axioms. I has total degree exactly 10: the degree upper bound is immediate and I(t,0,t,0,0,0,0)=2t^4*((4t^2+3t+4)^2+16)*((3t+2)^2+4) has leading coefficient 288. The variable z is the only local auxiliary coordinate in addition to the six term ports. This does not count the coordinates needed to encode an unbounded proof sequence, prior-row selection, axiom schemas, or bounded-universal elimination.

For relational Boolean contradiction, the top term e union not-e has code U(0,N(0))=20 and its complement has code N(20)=82. A theory proving the equality of those closed terms is inconsistent in its usual nondegenerate relational semantics. To derive a Con(ZFC) endpoint one must still explicitly supply a finite equational theory, its bidirectional syntactic consistency translation, its exact axiom codes, and the arithmetic closure compiler. None of those missing links is silently assumed by this note.

## Literature and limits

The direct relation-algebra route is represented by A. Formisano, I. Gavazzi, E. G. Omodeo, 'Diophantine Modeling of Provability in Algebraic Logic', CILC 2025, https://ceur-ws.org/Vol-4003/paper13.pdf . Their bijective term numbering uses Cantor pairing and their table reports a 4000-variable degree108 construction. The paper defers the concrete proper-axiom formulas to later work. This note's conservative treatment of missing codes is a small generic variant, not a claim of historical priority.

The reviewed ProveIt wave67 alternatives already cover Carl--Moroz direct provability, fixed-input universal machines, and constructive FRACTRAN. Fixed-input compilation is not a new proposal relative to that snapshot. The present local lemma has not been measured as a complete source and is not competitive evidence by itself.
