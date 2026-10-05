"""Portable finite checks supporting the fixed-alphabet theorem."""
from pathlib import Path
import sys,subprocess,json,time
root=Path(__file__).resolve().parent;start=time.time()
jobs=['check_constants.py','check_balanced_counts.py','check_lattice.py','check_recipe_small.py']
for name in jobs:
    print('Running',name,flush=True)
    subprocess.run([sys.executable,'-O',name],cwd=root/'checks',check=True)
record={'passed':True,'jobs':jobs,'seconds':time.time()-start,'scope':'Finite exact checks supplement the analytic proof; larger root-product decimals are orientation only'}
(root/'check_receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print('All checks passed',flush=True)
