from pathlib import Path
import subprocess,sys
here=Path(__file__).resolve().parent
for name in ('verify_nested.py','verify_small_supports.py','verify_marginal_barrier.py','verify_two_core_sector.py','verify_sector_formulas.py'):
 subprocess.run([sys.executable,str(here/name)],check=True)
print('All exact checks passed.')
