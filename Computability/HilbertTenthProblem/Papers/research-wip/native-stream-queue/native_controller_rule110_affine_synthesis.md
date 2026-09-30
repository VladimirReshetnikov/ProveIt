# A scoped obstruction to a direct Rule110 carry controller

No choice of four fixed integer weights, fixed affine offset, and three
distinct integer carry codes realizes **exactly** the minimal three-state
left-to-right Rule110 transducer using one scalar ternary symbol per
binary symbol. This statement covers all six injective maps from the
binary alphabet into {0,1,2}, and all choices of Boolean rail labels for
each desired transition.

The conclusion concerns equality of the local transition graphs. It does
not rule out a controller with extra states, a block code, serialization,
a compiler that detects uncoded symbols later, or universality of the
general filtered carry architecture. In particular eight assignment
patterns below force only an **uncoded output trit** as their exhibited
bad internal edge. Their behavior after that output is not classified.
No ordinary-input, boundary, or acceptance compiler is provided here.
The complete universal certificate bound remains76.

## 1. The precise transducer and embedding question

Rule110 has output0 on binary neighborhoods000,100,111 and output1
on the other five neighborhoods. Scanning a row from left to right,
the last two bits can be remembered by three states: A means the last
bit is0 (its predecessor is irrelevant), B means01, and C means11.
The resulting transducer is

| State | Read bit | Write bit | Next state |
| --- | --- | --- | --- |
| A | 0 | 0 | A |
| A | 1 | 1 | B |
| B | 0 | 1 | A |
| B | 1 | 1 | C |
| C | 0 | 1 | A |
| C | 1 | 0 | C |

This is only the local scan relation. Its use as a finite queue simulation
would additionally require row alignment, initialization and acceptance.

Fix any injective symbol map e:{0,1}->{0,1,2}. A scalar trit has exactly
the following Boolean rail representations:

    0: (0,0);       1: (1,0) or (0,1);       2: (1,1).

The proposed carry controller has arbitrary integer weights u0,u1,v0,v1
and offset h, with **every** Boolean label satisfying the equation
available as an edge:

    3 c_next = c_current + h + u0*d0 + u1*d1 + v0*a0 + v1*a1.    (1)

Suppose the states A,B,C have three distinct carry values. Exact direct
embedding means that, from each of those values and each input e(bit),
the transitions between the three values produce precisely the row in
the table. An edge with a wrong next state, wrong coded output, or output
outside e({0,1}) violates this exact local interface. Even this restricted
requirement, before considering edges to other carries, is impossible.

## 2. Finite exact algebra proof

For each of the six desired edges choose one of its possible rail
representations. There are finitely many such choices. If an embedding
exists, at least one complete choice is present in it, so enumerating
these choices loses no solutions. Each choice gives six homogeneous
linear equations (1) in eight unknowns:

    c_A,c_B,c_C,u0,u1,v0,v1,h.

Translating all state codes by a fixed amount changes only the freely
chosen offset. Thus impose c_A=0 as a seventh linear equation without
loss. Solve these equations over the rationals by exact linear algebra;
their nullspaces also parameterize all real solutions.

For each choice the [audit](native_controller_rule110_affine_synthesis.py)
proves one of two alternatives:

1. A difference between two of c_A,c_B,c_C is identically zero on the
   solution space. No injective state coding is possible.
2. The equation of an unwanted edge between these states is identically
   zero on the solution space. Every solution, including every one with
   distinct state codes, therefore includes that unwanted edge.

Each conclusion is checked twice: its linear form annihilates an exact
nullspace basis, and the receipt supplies rational coefficients expressing
it as a linear combination of the seven selected equations. Consequently
the verification is not a bounded search over coefficient magnitudes.
It covers all integer weights and offsets, and in fact all real ones.

The complete counts are

| e(0),e(1) | Rail assignments | Forced state collision | Other assignments | Only uncoded bad-output witness |
| --- | ---: | ---: | ---: | ---: |
| 0,1 | 128 | 88 | 40 | 4 |
| 0,2 | 1 | 1 | 0 | 0 |
| 1,0 | 32 | 24 | 8 | 0 |
| 1,2 | 32 | 24 | 8 | 0 |
| 2,0 | 1 | 1 | 0 | 0 |
| 2,1 | 128 | 88 | 40 | 4 |

All96 remaining assignment spaces have an unwanted internal edge;88
already have a wrong edge with a coded output. The other8 are rejected
for an output outside the selected scalar alphabet, as explicitly scoped
above. All322 assignments are therefore excluded for exact local graph
equality. The [receipt](native_controller_rule110_affine_synthesis.json)
records every assignment and its linear-consequence certificate.

## 3. Why an embedded subgraph is insufficient

There are simple choices containing all six desired transitions. For
example, take e(bit)=bit, carry codes (A,B,C)=(0,1,2), h=0, read
weights (4,6), and append weights (-1,-2). Choose the rails appropriately
at each transition and every row in the table satisfies (1).

But at carry0, the read1 label (0,1) and append0 label (0,0) also satisfy

    3*2 = 0 + 6.

This writes0 and enters C, whereas the intended A/read1 transition
writes1 and enters B. Both endpoint carries are intended states and the
output remains a coded bit. The arithmetic controller has no selector
that removes this edge. The audit includes the entire desired subgraph
and this explicit counterexample.

This explains the reason for auditing the full label graph. It does not
show that the extra transition makes every input accepted, or that no
larger encoding can handle it.

Run `python native_controller_rule110_affine_synthesis.py` to compare a
fresh exact audit with the receipt. Independent full proof/source review
and default-receipt replay pass, including the complete assignment count,
all row-space certificates and the distinction between88 coded-output and
8 only-uncoded-output witnesses. No findings were reported.
