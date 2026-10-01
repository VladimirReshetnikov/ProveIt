from pathlib import Path
import subprocess,sys
here=Path(__file__).resolve().parent
for name in('check_matrix_lifts.py','check_kernel_compression.py','check_reductions.py','check_eventual_scaling.py','check_rank_three_boundary.py'):
 subprocess.run([sys.executable,str(here/name)],check=True)
print('All exact checks passed.')
