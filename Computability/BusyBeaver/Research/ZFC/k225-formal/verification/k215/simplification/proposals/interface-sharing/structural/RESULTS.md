# Round12: concrete small checker refactor, not a new foundational proposal

Pin: `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

The current literal and normalized Lean certificate front ends still duplicate the entry-dispatch Boolean definition and its soundness case split. A minimal implementation of the previously proposed adapter sharing is included as `ENTRY_DISPATCH.patch`, with proposed files and a portable, self-authored `build_proposal.py`. No received script was executed.

## Exact result

The audit establishes byte-identical seven-line entryOk definitions and seventeen-line entryOk_good proof bodies. The only semantic difference between the clients occurs in branchOk and its soundness theorem, not in dispatch on the two observed leaf opcodes.

Factor a function `entryCheckWith decode t1 t2 branch x`, and prove:

    (∀ {A B j}, branch A B j = true → BranchGood t1 t2 S A B) →
    entryCheckWith decode t1 t2 branch x = true →
    EntryGood t1 t2 S (decode x.1) (decode x.2.1).

Its proof is exactly the existing case split. A halt pair is immediate. A decrement pair must have equal register indices and two successful branch checks; the hypothesis supplies the two BranchGood witnesses. Every other opcode combination rejects. The theorem does not assume lookup totality, a balanced layout, decoder injectivity, path normalization, equality-check completeness, or a register invariant.

Both front ends retain their existing branch checkers, relations, lookup proofs and saturation logic. Their public entryOk definitions become transparent wrappers, and entryOk_good becomes a two-line specialization. The generated Boolean expressions are definitionally the same after unfolding. The original decoder remains128-fuel; the concrete K215 use of its512-fuel decoder remains untouched. Consumed paths are unchanged before increment/break.

Source counts, including abstraction and adapter overhead: RMBisim579→593, RMNormalizedBisim166→146, total745→739, net6 lines removed. Thus this is a small maintainability improvement, NOT a large proof reduction. The gain is eliminating a duplicated opcode-pair case analysis and making future front ends supply only branch soundness.

## Adoption and novelty

Phase12 did not change these certificate modules. Round11 already recommended sharing normalized/literal checker adapters using a more general endpoint-equality interface. This patch is a deliberately narrower concrete implementation of that recommendation, not a newly discovered architecture. It avoids touching path equality, layout, or the already sound generic Bisim theorem.

For Rocq, the same entry-dispatch interface is applicable after the previously recommended common semantic BranchGood/EntryGood layer is extracted. No new Rocq source reduction is claimed here: the maintained Rocq adapters still have a different semantic organization, and the generic semantic-core recommendation is prior work.

## Alternative investigated and not recommended yet

KSim.halts_iff contains a positive-stuttering halting simulation proof with strong induction and run-length subtraction. A generic deterministic positive-stuttering theorem would subsume it. However, the inspected RMEquiv proof has nested structured-run reasoning, not the same simple interface; no second straightforward Lean client was found. Introducing the general theorem solely to relocate one35-line proof is not a demonstrated simplification. The initial progress requirement must not be weakened to reflexive reachability, which would make halting reflection false.

## Validation limits

The portable audit was run and passed. It reads only bundled source snapshots, checks exact duplicated blocks, writes the candidate and patch, and records source hashes/counts in AUDIT.json. Neither Lean nor Rocq is available on PATH here. The patch is UNCOMPILED; require compilation of both modules and their concrete K215 clients, unchanged public theorem statements/axioms, and ordinary kernel checking before adoption. No build-time improvement is asserted.
