# Independent source review: 13-parent→88 ring cuts

The Fin14 extension preserves parent slots except sigma at slot 8 and adds t at slot 13; projection with the old parent root restores the Fin13 valuation. The three nonfirst fields transfer through the reviewed reverse cuts, and the target first residual has the stated `[M(ell+k−sigma)+Yb]²−M²D` sign and scale.

The checker tests full literal graph evaluations modulo 12 and 97, pins the previously passed component reviews and replays the author source receipt. It does not rerun those independent reviews, derive the guard or elaborate Lean. Run `python3 -I -S -B check.py` and compare with `result.json`.
