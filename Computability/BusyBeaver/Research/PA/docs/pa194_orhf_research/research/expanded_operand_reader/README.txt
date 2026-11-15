Expanded operand-reader grammar search

This is a bounded discovery search. No sub-194 machine was found.
It exposes the single node75 occurrence in the AX11H emitter into
((node32,(node53,node55)),node65), leaving the existing fixed reader 213
and all its original uses in place. The emitter word grows from 190 to 193
macro tokens. The new atom controls are 104=node32 and 107=node53. The
compiler recognizes the already present fixed subtrees:
 (107,98) ->185, (104,185) ->92, (92,90) ->213.
The initial expanded and original source instruction arrays were checked
identical. Acceptance of any discovered endpoint would additionally require
exact source-graph equality, full runtime checks, and blank initialization.
No endpoint below the original score 60 was found.

The C++ objective is the number of allocated AX readers minus compatible
context folds, plus explicit scanner penalties. The fixed part has 134
working controls, so a zero-penalty effective score 59 would be a nominal
193-state candidate, still requiring the universal acceptance checks above.
The initial and best observed score was 60. Associativity moves rewrite
all occurrences of a selected DAG subtree together. No parameter renaming
is enabled in this experiment, because expansion changes source-word offsets.

The original-fixedpart run requested 300 seconds (seed 147) but was killed
by resource pressure, exit 137. Its log is a partial prefix, not a completed
300-second search. The second run uses the known B dedicated history selector
in the fixed part, seed 148, with the same search binary. That run completed 2,216,629 proposals in 240.005 seconds, with 375,878
accepted moves, zero saved sub-194 hits, and best penalized score 60.
The first run has at least 1,604,000 completed, flushed proposals; its
last flushed elapsed time is 138.146 seconds. Negative randomized screens are not
lower bounds on Turing-machine state complexity.

Portable regeneration of deterministic inputs (Python 3 standard library):
    python3 -B setup.py
Compile and rerun the optional searches (C++17):
    g++ -O3 -std=c++17 search.cpp -o search
    ./search templates.txt leaf_attrs.txt replay147 300 147
    ./search templates_B.txt leaf_attrs.txt replayB148 240 148
The stopping criterion is elapsed wall time, so replay proposal counts depend
on the machine and concurrent workload. Seed fixes the random proposal stream
until timing ends it. Successful searches would write hit*.grammar.json.

Attribution: screen.cpp and search.cpp derive from search/screen.cpp and
search/search_exact.cpp of the primary PA194 research packet. Modifications
add three fixed-subtree recognizers, two leaf names, disable the old
parameter-renaming moves, and restrict saved hits to score 59 or better.
The nodes/grammar/fixed input and Python compiler/runtime come from the
supplied AX11H/ORH packet. Keep the enclosing research package's upstream
James Chang, Wade, and ProveIt notices. 
