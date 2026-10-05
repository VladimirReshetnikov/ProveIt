"""Run the exact combinatorial, coefficient and inverse checks."""
from pathlib import Path
import subprocess,sys,json,time
root=Path(__file__).resolve().parent
rows=[]
for name,args in [('check_midpoint.py',[]),('gaussian_corrections.py',[]),('ward_corrections.py',[]),('check_gaussian_integrals.py',[]),('check_inverse.py',[]),('generate_expansion.py',['--order','2'])]:
    start=time.monotonic()
    subprocess.run([sys.executable,'-O',str(root/'code'/name),*args],check=True,cwd=root/'code')
    rows.append({'script':name,'arguments':args,'seconds':round(time.monotonic()-start,3)})
(root/'verification.json').write_text(json.dumps({'passed':True,'checks':rows},indent=2)+'\n')
print('All exact checks passed.')
