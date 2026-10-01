from pathlib import Path
import subprocess,sys
here=Path(__file__).resolve().parent
for name in ('verify_certificate.py','verify_barrier.py'):
 subprocess.run([sys.executable,str(here/name)],check=True)
print('All exact checks passed.')
