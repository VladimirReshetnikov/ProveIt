# Dominated-rho8 theorem and command compiler

## Proven result

For raw natural-number codes with

```
P(a,b) = (a+b)*(a+b+1)/2 + b
I(a,b) = 4*P(a,b)
L(A,B,C,U) = ((C -> U) -> A) -> ((A -> C) -> (B -> C))
```

truth code 0 and modus ponens, the family of L instances restricted to
`U <= A` derives every unrestricted L instance. Consequently replacing
only this row in K219 preserves **every** derivable numerical code. The
proof allows zero arguments and the exact native alias `I(0,0) = 0`.

The standalone paper `dominated_rho8.tex` also supplies an exact command
compiler for a three-field AX instruction, with additive fields read
only by MP and AX. Both XY fields `[c+3,x,y]` and YX fields
`[c+3,y,x]` are covered explicitly. The included section
`dominated_common_input_calibration.tex` gives a second exact compiler
retaining the original common additive input and the original MP, DROP,
and NIP branches. Its AX wire order is `[c+3,z,y,x]`, with
`U=D+z`, `A=U+x`, and `B=H+y`. Both implementations have cofinal
exhaustive search from arbitrary safe clean seeds and extend to six
arbitrary control/scratch fields using the unchanged fetch/selector
prefix. The common-input section identifies the independently checked
203-subtree source and separates this fact from any binary startup claim. Binary transition
counts, exact physical initialization, and runtime contracts belong to
the surrounding construction; this theory directory makes no independent
claim about a binary machine's state count.

## Check the finite theorem

Run with Python 3 and the standard library:

```
python check_classical_compact.py dominated_rho8_full_certificate.json
```

Expected result: `verified: true`, 3,728 proof nodes, 5,160 shared terms,
and unrestricted-rho8 root 3727. There are 1,260 dominated-row leaves,
one truth leaf, 55 MP steps with explicit substitutions, 410 direct
substitution steps, and 2,002 direct MP steps. All nonzero fourth
arguments at axiom leaves are literal subterms of first arguments; the
maximum subterm depth is four. The checker does not invoke unification,
proof search, a theorem prover, Lean, or Rocq.

`cd59_certificate.json` separately contains the 58-node proof closing the
prior conditional `cd59` gap. Its only new axiom context is
`A = (((z -> U) -> v) -> w)`.

## Rebuild the certificate

```
python build_full_rho8_certificate.py
python check_classical_compact.py dominated_rho8_full_certificate.json
```

This rebuild works from any current directory. It reads the supplied
prior fragment DAG, pinned `CD230.v`, and saved Prover9 proof. It produces
the small cd59 certificate, a basis certificate, and the final unrestricted
row certificate. The builder uses unification to obtain candidate
substitutions; the independent checker only evaluates the resulting
explicit substitutions. The proof search need not be rerun.

`contexts_hyper.in` and `contexts_hyper.out` retain the successful search
input and output. They were produced using Prover9 from
<https://github.com/ai4reason/Prover9>; that software is not a dependency
of checking or rebuilding the finite certificate from the saved proof.

## Provenance

The ProveIt repository snapshot was pinned at
`f8ec6158f3bdc885139ee395ae34fe44c3251b9f`.

* `evidence/bounded_cd_refined_result.json`: prior 1,000-node dominated
  fragment DAG, from the incoming `research218_progress_latex` research
  companion, `checks/dominated/`.
* `evidence/CD230.v`: pinned retained implicational derivation from that
  same companion, `evidence/logic/CD230.v`.
* `evidence/KCode222.lean`: current numerical calculus interface copied
  from `Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/`
  `singleton-search/inputs/` at the pinned repository snapshot. The
  current K219 inherits its numerical row and gated bundle definitions.
* `evidence/DirtyProgram254.lean`: the earlier root-absorption composition,
  from `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/` at the pinned
  snapshot. Its 219-node register DAG is not a 219-state binary machine.
* `evidence/dirty_seed219.tex`: the current-source mathematical absorption
  argument supplied by this session's source/runtime investigation.
* `evidence/common_source_receipt.json`: exact common-input source
  construction and CFG verification, including the 203-subtree candidate
  hash, all 186 retained outside-AX leaf paths, and 6,176 guarded cases.

`manifest.json` records SHA-256 digests. Existing source notices and
attributions remain in the copied files. The new proof certificate is
checked independently of every historical source; provenance files are
needed only to reproduce its construction.

## Scope

The theorem and command compiler are ordinary mathematical proofs whose
finite and primitive-recursive transformations can be formalized in
ZFC. No newly compiled Lean/Rocq endpoint for the modified source is
claimed by this directory. The final machine report separately records
physical runtime verification and blank-tape startup evidence.
