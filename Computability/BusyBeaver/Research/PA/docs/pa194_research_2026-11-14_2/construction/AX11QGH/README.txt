PA194AX11QGH -- complete 194-state construction
=============================================

This directory is a portable construction of one new blank-start binary
Turing machine, with a written mathematical iPRA consistency-equivalence
proof relative to the explicitly identified inherited PA calibration.
It contains no claim of an end-to-end kernel-checked Lean theorem and no
claim that 194 is a lower bound.

Literal machine
---------------
machine/machine.tm has 194 working states, start 0, and terminal halt 194.
The tape is two-way infinite, alphabet {0,1}, initially all zero; the head
starts at position 0. The halt state has no rows and is not counted. There
are 388 rows: state read write L_or_R next_state.

Dense SHA-256:
513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1
Native SHA-256:
6a97ad509ba5f811e110659bbc36265a0da84015e5e53b883234a4d1a048a452

The native presentation starts in 74 and halts in 254; labels.json gives the
exact dense/native map. Working labels are not state counts.

What's new
----------
AX now combines its eleven-entry/four-operand protocol with the saved
generalization U(c,h), where c is its first operand and h is the incoming
cached theorem. Shift tests only h=1. Successful MP returns the visible
conclusion and pushes no zero. The inherited Q orientation of h6 is
explicitly included in the full name. Early working logs use AX11GH as an
alias for exactly this same table, never a different sixth head.

The exact interface is
 AX(c,x,y,z)(t,w,d,h) = (0,[q0,...,q9,t;w],z,0),
 D=d+x, H=h+y, q9=U(c,h).
The complete other nine heads appear in proof.tex. The fourth operand z
is genuinely decoded. It is not implicitly fixed to zero.

Local operations:
 Push = AX(0,0,0,0);Shift^10;MP(0)
 Pop  = AX(0,0,0,0);Shift^12
 Gen(i) = Push;Shift;AX(i,0,0,0);Shift^11.
Pop halts exactly when its saved visible top is 1. Generalization remains
total, even on input formula 1. A refutation ends with Pop, not plain Shift.

Reproduction
------------
Python 3.10 or newer and its standard library suffice. Keep assertions
enabled; do not use -O or PYTHONOPTIMIZE.

 python3 -B verify_all.py

The individual stages are:

 python3 -B build.py
 python3 -B check_commands.py --machine machine --output evidence/commands.json
 python3 -B independent/check.py machine --output evidence/independent
 python3 -B physical_ipra_audit.py --bundle . --output evidence/physical_closure.json

build.py --quick skips only the construction symbolic replay, and records
that omission. It is not equivalent to running the full commands above.
verify_all.py --quick skips both per-site symbolic tape replays, checks all
regenerated literal/source files, the universal command equations and the
recorded endpoint/duration bindings, and records the omission. The default
mode replays everything.
The independent checker imports neither the builder nor its block oracle.
It proves four generic list lemmas from literal transition rows, then
checks every instruction outcome on arbitrary symbolic register values,
spare lists and gap sizes. This may take several minutes.

Construction facts
------------------
 134 fixed controls  + 67 raw readers  - 7 simultaneous folds = 194.
 28 complete local two-cell fold cases.
 3671 primitive source sites; 4778 source outcome contracts.
 All arithmetic-box transition rows remain unchanged.
 Complete finite-support blank startup reaches the intended source frame
 in 57,922 transitions (native dispatcher 84, head -2, logical seed [2,0,...,0]).
 The closure audit checks all 4,777 nonhalting padded addresses, zero
 overflow, zero affine head motion, all 13 duration coefficients nonnegative
 and each duration's constant at least 3. The sole halt case has duration 3.

The final source graph is exactly the accepted QAX11H association populated
with the single generalizer token change copyD -> copyA at position 1.
Both the whole source instruction graph and all successors are compared.

Proof and provenance
--------------------
proof.tex gives the full new command proof, including selectors, reserved
zero for MP, four-field scheduling, proof annotations and quantifier-free
bounded-input induction. It identifies the source/tape and numerical/PA
calibration dependencies in the incoming AX11H packet at ProveIt commit
1e1a41f799d4658b829cdd0eabae3775a0c8c4a0. That packet supplies a written
weak-base completion; its Lean formalization remains incomplete.

Inputs are from pa194_ax11g_research_2026-11-14 and
pa194_ax11h_research_2026-11-14 at that pinned commit. Their earlier inputs
come from James Chang's PA196 development, the PA194 grammar/runtime work,
and the supplied Q, G, AX11 and H transformations. The original licenses
are retained under licenses/. The supplied compiler/support/runtime and
independent literal engine remain attributed to their upstream sources.

The new work consists of the combined table, candidate-specific exact
source/fold/blank bindings, the command checker adaptation and the complete
AX11QGH proof. Numerical-calculus calibration is reused with its actual
written-proof status, rather than advertised as a new formal verification.
