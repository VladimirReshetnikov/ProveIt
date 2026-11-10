# Sign20 conditional lower bound: symbolic count failure

Author-observed outer session `88800` exited 1. The first five stages passed;
the sixth left both symbolic `List.count` goals unsolved because simp did not
expand `List.count_cons`. Both counts and dependent seed coefficient report
`sorryAx`; no sixth-stage object, lower theorem or postflight is claimed.
The [independent failure audit](../../../reviews/nine-sharing-sign20-full-coeff-retry02-failure-independent/README.md) passed; the packet is frozen.
