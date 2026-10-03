# Source provenance and documented corrections

## Primary universal machine

Turlough Neary and Damien Woods, “Four Small Universal Turing Machines,”
Fundamenta Informaticae 91 (2009), 105–126.
DOI: https://doi.org/10.3233/FI-2009-0008
Author-hosted primary PDF: https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf

The literal U15,2 table is Table 16 on printed page 121, PDF page 17. Mapping
c=0, b=1 and u1,...,u15=A,...,O, an independent comparison matched all 30
entries to the bundled tm_table.json and its pinned compact serialization.
The only undefined entry is u10,b, represented by J1.

The halting display on printed page 123, PDF page 19 underlines b. It agrees
with Table 16 and the literal source. The prose immediately below instead
says u10,c. This is recorded as a discrepancy in the primary prose; no
author-issued erratum is asserted and no table repair has been inferred.

Equation (3), Definition 3.1 and Table 1 specify finite program/data encodings,
initial state u1 and blank c. Section 3.5 proves the corresponding U15,2
simulation. The invocation is standard finite-input universality with blank
tails, not an infinite periodic-background weak-universality assumption.

## Pinned reusable dependency

The bundled source-replay directory is copied from the previously delivered
two-counter source package. Its literal table is 8408 ADD/SUB rows, compiled
from 528 three-counter rows by the all-input prime-macro proof included there.
The current binary CA construction is proved for every supplied source table;
universality of this particular instance additionally uses that exact source
simulation and the primary finite-input universality theorem.

Important pinned hashes:

- source-replay/source/literal2.json:
  85e16b44828f2f3d4ad6d0805dcc9e9922893a6d286874f2018d6a33af864b00
- source-replay/source/UniversalTM15x2.tm.txt:
  ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae

The complete bundled data, proof and verifier bytes remain unchanged. In
particular, UniversalTM15x2.tm.txt contains an old bibliography comment giving
the incorrect pages 123–144. It is deliberately retained byte-for-byte for the
existing pin; the correct primary pagination is 105–126, as documented here.
This is a correction to the new package's citation, not a change to the old
delivered package or the pinned source machine.

The source verifier was rerun locally. It passed 4475 symbolic affine paths
covering every one of the 528 virtual and 8408 physical rows, plus the listed
finite supplementary tests. Those paths compose with the included decreasing-
rank arguments for all-input simulation; finite replay alone is not presented
as a universality proof.

## Existing work and scope

A targeted read-only search of VladimirReshetnikov/ProveIt at commit
c8e503d8ab4b4d7e237f65e88155ceda17800a52 found the earlier abstract-level
five-numerical-particle provenance but no reusable five-particle CA table in
the inspected results. No repository was cloned and no public write was made.
This is a bounded search, not evidence of novelty or absence of related work.

The present construction and its tests are ordinary mathematical arguments
and executable checks prepared with AI assistance, not a machine-checked
formalization. No priority, current-record or optimal-radius claim is made.
