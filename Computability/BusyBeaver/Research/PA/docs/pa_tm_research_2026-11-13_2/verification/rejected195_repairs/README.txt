REJECTED 195-STATE TABLE: FOCUSED REPAIR SEARCHES

No valid sub-196 machine is asserted.

python3 repair_candidate.py
  Replays the 37,584 one-extra-row alternatives on 48 rows of the failed
  source26 trace. 153 repair that contract; none retain all other cases.

python3 two_row_dispatch.py
  Replays 15,680 interactions using five specified left-reading helpers.
  113 repair source26; none retain all 4,959 cases.

Both scripts use only standard Python and the sibling zero_jump_machine
verifier. Their exact search grammar is documented in each source file and
receipt. These are negative results within those grammars, not state lower
bounds. The negative input has sparse dense labels, 195 working states,
start0 and halt196. Its source binding is known to fail.
