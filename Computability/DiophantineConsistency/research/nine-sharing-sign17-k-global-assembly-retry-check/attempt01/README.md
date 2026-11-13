# Global K candidate-rank assembly: failed cast retry

Author-observed outer session `54087` exited 1. The four rank stages passed;
the final stage reduced the failure to the two chunk00 branches, where
`Fin.castLE` still wraps a variable. Reports contain `sorryAx`; no final
assembly object or postflight exists. The [independent failure audit](../../../reviews/nine-sharing-sign17-k-global-assembly-retry-terminal-independent/README.md) passed; the packet is frozen.
