"""Replay every scalar proof certificate with the Python standard library."""
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
for name in ['verify_green_constants.py','verify_weighted_outer.py',
             'verify_pressure_separation.py','verify_coefficient_lower_bounds.py',
             'verify_weighted_cutoff.py','check_sharp_endpoint.py']:
    subprocess.run([sys.executable,str(root/name)],check=True)
print('Every scalar certificate passed.')
