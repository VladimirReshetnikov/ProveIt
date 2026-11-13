# Independent terminal audit of five-norm extraction

The post-hoc author record reports outer session **76122, exit 0**. The
retained state records successful dependency and compile runs, with no monitor
stop, descendant or monitor error; the compile log is empty and no axiom
report was requested. The output object remains under
`/tmp/nine-sharing-norm38-five-norms-check-v2-20261105/lib/DiophantineConsistency/`,
SHA-256 `ea31b12a3933596dc35448c05a91b17dcb3c915ff8ed13c603caf161d136051d`.

The checked `seed_zero_fiveNorms` theorem is generic over an IΣ₁ model and
four integer ports represented by model-natural values. Assuming those four
cast equalities and a seed zero at distinguished input 1, it proves the
static `fiveNorms` predicate. In order, these are N0=1, N1=1, Na=1, Nt=1 and
scaled_Ns=Delta. This is the separately source-reviewed five-norm statement;
it does not establish `gatesHold`, source-graph evaluation, the reverse
construction, a complete model equivalence or an iPRA endpoint.

`check.py` verifies source equality with the reviewed draft, the state and
logs, the object, all 250 candidate direct guard slots and 1,077 overlay links.
It independently authenticates the immediate each-slot producer and the
three successful batch group producers 03, 05 and 09 against their recorded
source/object/log hashes and direct guards, and checks the candidate's import
links resolve to those exact objects. The batch's overall state is failed only
because its separate final assembly timed out; that failed object is not used.

The outer receipt is an author record, not a raw transcript or independently
observed historical exit. These are retained-evidence and current provider
point checks, not a Lean replay or complete transitive/dynamic-load audit.
Between-observation changes and sampled resource limits remain. No Lean
process was run by this review.
