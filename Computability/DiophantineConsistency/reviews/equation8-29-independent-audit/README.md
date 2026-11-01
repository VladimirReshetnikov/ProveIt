# Independent provisional 29-variable display audit

This finite display and graph audit covers the provisional PDF (SHA-256 `131a65e22006fc0056318baf5b4a87f5dfa205c4466d3df60bc26ce69ceb6bed`). It checks all 135 candidate and printed circuit gates, 29 variables, four fixed ports, 40 displayed definitions and 20 residual squares; checks graph topology and liveness; and tests display and circuit mutations. The separate scope check verifies the candidate disclosure, W and f-square aliases, and deletion of the former f-square input. Two clean builds reproduce the PDF byte-for-byte. Both pages were visually inspected; the layout log reports small font substitutions and no overfull or underfull boxes.

This packet checks the graph and displayed formula, not a Lean literal or model transport. The PDF explicitly states that model witness transport and native iPRA equivalence were not yet established when it was generated. A later proof or replay must be assessed separately.
