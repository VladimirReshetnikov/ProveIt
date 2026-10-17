`Code254ProofCompiler.lean` defines a structural function from the twelve
`Code254Proof.RawProof` constructors to the existing `Enum254` command
blocks. MP compiles both children with its recorded output; GEN compiles
its child with its recorded binder; each axiom uses the matching leaf and
the bundle uses `bundleLeaf`. The function consumes finite data and uses
neither proposition elimination into data nor witness selection by Choice.

The proposed `compile_contract` theorem validates each node before using
the existing block contract. Its guarantee preserves the saved stack and
returns the recorded conclusion with zero accumulator and cache, or halts
earlier. In particular, it does not assert that every valid block always
returns normally from arbitrary working data.

For a valid tree whose conclusion is the falsity code, `refutationWord`
adds the existing initial reset command and the three terminating commands
from `Enum254.complete`. `refutation_cexec_none` states that this explicit
word halts from every working state. `refutation_halts` then invokes the
existing scheduler coverage theorem. The command semantics and proof
blocks retain Enum254's attribution to Mira-Cult's published calculus and
enumerator.

The fresh source check passed with the explicitly pinned Lean 4.32.0
executable in 0.438 seconds. Seven caller checks passed in 0.257 seconds,
covering the truth word, an axiom leaf, GEN, MP, arbitrary working states
and the scheduler endpoint. The three main theorem axiom reports contain
only `propext`, `Classical.choice` and `Quot.sound`; the structural compiler
function itself makes no Choice-based selection. The check reused
source-matched dependencies rather than rebuilding the entire closure.
Exact commands, hashes, output and the caller source are retained in
[the verification record](results/code254-proof-compiler-verification.json).

This adds an external proof-data compiler; it does not prove that its code
is represented in PA, prove internal arithmetic totality, or change the
binary table or its consistency calibration.
