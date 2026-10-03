"""Run every exact certificate and regression check."""
from pathlib import Path
import subprocess,sys
HERE=Path(__file__).resolve().parent
for name in ["verify_transversal_lift.py","verify_full_lift.py","verify_line_matroid.py","verify_union_formula.py","verify_forced_core.py","verify_star_scaling.py","verify_negative_shapes.py"]:
 print("CHECK",name,flush=True)
 subprocess.run([sys.executable,str(HERE/name)],check=True)
print("All exact checks passed.")
