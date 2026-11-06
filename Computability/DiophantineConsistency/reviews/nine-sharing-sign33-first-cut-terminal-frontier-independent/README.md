# Independent review: first-cut failure

The retained dependency check exited 0 and Lean compilation exited 1 on applying `List.mem_cons_self` as a function. The author-recorded outer session 98588 exited 1. The first evaluation declaration printed `[propext, Classical.choice, Quot.sound]`, but the module produced no successful object; the second declaration's `sorryAx` report is error-contaminated and is not evidence of the desired cut. The final whole-run survey and postflight were not reached.

The checker validates the source, state, retained logs and author observation, selected square-sum dependency, 100 recorded guard slots and 1,173 overlay links. These are point-in-time observations. No Lean replay was made and the author observation is not an independent raw terminal transcript.
