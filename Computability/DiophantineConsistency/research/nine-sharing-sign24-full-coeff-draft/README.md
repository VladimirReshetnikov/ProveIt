# Sign24 full axis coefficient composition draft

These source-only stages build on the checked N0 and weighted residual
ingredients. They propose proving that a residual of axis degree at most two
has square with zero eighth coefficient, that the N0 square has coefficient
one, and that the coefficient of a list of remaining residual squares equals
the number of N0 rows. The concrete seed list is then checked to contain N0
once, yielding coefficient one for the seed evaluated on the axis.

The final source proposes the connection from seed evaluation to the direct
Fin24 polynomial and its total-degree lower bound. None of these sources is
compiled and they may require further proof repairs. Combining a checked
lower bound with the checked upper bound remains another stage. No JSON/byte
or PDF binding follows.
