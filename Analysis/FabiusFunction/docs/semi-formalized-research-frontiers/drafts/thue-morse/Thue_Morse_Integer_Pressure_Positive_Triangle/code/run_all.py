from pathlib import Path
import subprocess,sys
root=Path(__file__).resolve().parent
for name in ['check_triangle.py','check_basis_signs.py','check_m2_cubic.py']:
    subprocess.run([sys.executable,str(root/name)],check=True)
print('All exact checks passed')
