# Independent revised 29-variable display audit

This finite audit covers the revised provisional PDF (SHA-256 `5c93c532f9a27e4312311ee0680b046177b8b3793f9a90b705d306276dcb3016`). It checks all 135 candidate and printed circuit gates, 29 variables, four fixed ports, 40 displayed definitions and 20 residual squares; checks graph topology and liveness; and tests display and circuit mutations. Two clean builds reproduce the PDF byte-for-byte. Both pages were visually inspected; the layout log reports small font substitutions and no overfull or underfull boxes.

The scope check ties the revised wording to the historical matched model receipt and the failed native replay observation, and checks the W and f-square aliases. It checks receipt, source and log hashes but does not rerun Lean or the provider closure; some provider dependencies are now unavailable. It does not establish native equivalence. The earlier candidate audit remains historical.
