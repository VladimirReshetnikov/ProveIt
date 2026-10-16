# Capture, Collection, and disjoint tags

## Source and scope

Harvey M. Friedman, *Simplified axioms for class theory*, 15 September
2020, **Theorem 3.21, printed page 19** (PDF page index 18):

https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2020/09/NBGAxioms091520.pdf

The displayed proof uses Capture to derive Collection after limited
comprehension has been established. Its untagged extraction step needs
repair: covering an input set by the union of a selected family of
unordered pairs does not ensure that every input appears as the first
component of a selected encoding. The finite example below demonstrates
that particular inference failure. It does **not** refute the theorem
that Friedman's finite presentation is equivalent to his NBG.

## Exact finite counterexample

Use the von Neumann ordinals

\[
0=\varnothing,\quad 1=\{0\},\quad
2=\{0,1\},\quad 3=\{0,1,2\}.
\]

Let \(A=\{0,2\}\) and let \(\phi(x,y)\) hold exactly for
\((x,y)=(0,1)\) and \((x,y)=(2,3)\). This relation is total on
\(A\). Form the displayed untagged encoding

\[
B=\{\{x,\{x,y\}\}:x\in A\land\phi(x,y)\}.
\]

Since \(\{0,\{0,1\}\}=\{0,2\}=A\), the set \(C=\{A\}\)
satisfies

\[
C\subseteq B,\qquad A=\bigcup C.
\]

Nevertheless the encoding \(\{2,\{2,3\}\}\) is not in \(C\):
coverage of the input \(2\) occurred through the second component of
the encoding for input \(0\). Moreover,

\[
\bigcup\bigcup C=\bigcup A=2=\{0,1\},
\]

which omits the unique required witness \(3\) for input \(2\).
Thus neither the claimed input coverage nor the proposed double-union
witness bound follows from these Capture conclusions.

## Tagged repair and its assumptions

Assume Extensionality, two distinct set tags \(0\ne1\), Pairing,
Union, Power Set, limited class comprehension, and that every subclass
of a set is a set. Limited comprehension here permits quantification
over sets and the available class parameters. Assume Capture in the
form

\[
a\text{ is a set}\ \land\ a\subseteq\bigcup B
\ \Longrightarrow\
\exists C\,[C\text{ is a set}\ \land\ C\subseteq B
                       \ \land\ a\subseteq\bigcup C].
\]

Let \(A\) be a set and \(\phi(x,y)\) an available limited formula
such that every \(x\in A\) has a **set** witness \(y\).
Use ordinary Kuratowski ordered pairs

\[
\langle u,v\rangle=\{\{u\},\{u,v\}\},\qquad
a_x=\langle0,x\rangle,\qquad b_y=\langle1,y\rangle.
\]

Define

\[
A_0=\{a_x:x\in A\},\qquad
B=\{\{a_x,b_y\}:x\in A\land\phi(x,y)\}.
\]

The formation of \(A_0\) does not require Replacement. Put
\(U=A\cup\{0,1\}\). For \(x\in A\), both \(\{0\}\) and
\(\{0,x\}\) belong to \(\mathcal P(U)\), so

\[
a_x\in\mathcal P(\mathcal P(U)).
\]

Limited comprehension and the subclass-of-a-set principle therefore
make \(A_0\) a set. The class \(B\) exists by limited comprehension;
it need not be a set. Totality of \(\phi\) gives
\(A_0\subseteq\bigcup B\). Capture yields a set \(C\subseteq B\)
with \(A_0\subseteq\bigcup C\).

For any \(x\in A\), choose a covering member
\(c=\{a_u,b_y\}\in C\), where \(u\in A\),
\(\phi(u,y)\), and \(a_x\in c\). Kuratowski injectivity and
\(0\ne1\) exclude \(a_x=b_y\), so \(a_x=a_u\) and \(x=u\).
Consequently \(\phi(x,y)\), with the membership chain

\[
y\in\{1,y\}\in b_y\in c\in C.
\]

It follows that \(y\in\bigcup^3 C\). Three applications of the
set Union axiom supply a set \(W=\bigcup^3 C\) satisfying Collection:

\[
\forall x\in A\ \exists y\in W\ \phi(x,y).
\]

This proof uses neither Replacement nor Collection to construct its
inputs. It needs no simultaneous selection of witnesses, and hence no
Choice. Foundation and Infinity are unnecessary for this conditional
lemma once the two distinct tags are available. It repairs the
displayed extraction step, without claiming an independent audit of
every earlier lemma in the source manuscript.

## Executable finite regression

[capture_tagged_check.py](../code/capture_tagged_check.py) represents
hereditarily finite sets by immutable finite sets. It checks the exact
untagged counterexample, disjoint tagged ranges, the double-power-set
bound for \(A_0\), and every subfamily of the finite tagged \(B\)
that covers \(A_0\). For this example exactly one tagged subfamily
covers \(A_0\); its triple union supplies all required witnesses.

Run from the archive root:

```sh
python code/capture_tagged_check.py
```

The captured output is
[capture_tagged_results.json](capture_tagged_results.json).
The finite regression illustrates the general proof and its former
failure mode; it is not a finite model of the full class theory.
