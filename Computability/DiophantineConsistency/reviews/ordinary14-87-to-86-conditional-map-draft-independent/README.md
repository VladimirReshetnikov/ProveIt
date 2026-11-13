# Independent source review: conditional 87→86 map

The proposed reverse coordinate is `h=omega−C*K`. The proof retains both explicit strict assumptions `F+alpha<q` and `C*K<omega`: the first justifies the C cast, and the second both makes h positive and justifies the final subtraction cast. The beta/K port casts, same 87 zero, and output equality direction align. Equality `C*K=omega` would instead give h=0, so the strict bound is significant.

The checker tests bounded strict cases and replays the author and forward-client reviews. It does not derive either strict hypothesis from an 87 zero, run Lean, or establish unconditional equivalence. Run `python3 -I -S -B check.py` and compare with `result.json`.
