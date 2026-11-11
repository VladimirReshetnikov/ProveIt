# K215 forward check 09: proposed split

This source-only proof refactor selects the two actual children of `fwd9`, checks each child's `allC fwdF` predicate in a separate module, then joins them in the original theorem. The original file remains untouched. The two match expressions and definitional `change` target must be checked by Lean; feasibility under unchanged limits is not yet known.
