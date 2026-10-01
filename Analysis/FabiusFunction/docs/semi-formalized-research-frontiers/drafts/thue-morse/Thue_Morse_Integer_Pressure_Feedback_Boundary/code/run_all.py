"""Quick exact validation of the included analytic and finite certificates."""
from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
for name in ['verify_cutoff.py','check_trace_coverage.py','check_m2_response.py','check_m2_pressure.py']:
 subprocess.run([sys.executable,str(root/name)],check=True)
print('All packaged certificate checks passed; use reproduce_all.py to regenerate every matrix enclosure')
