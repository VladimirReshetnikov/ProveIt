"""Run the exact local checks; no network access or guessed recurrence."""
from pathlib import Path
import subprocess,sys,time,json
root=Path(__file__).resolve().parent;start=time.time()
jobs=[['check_kernel.py'],['direct_terms.py','30'],['check_jets.py'],['check_second_correction.py'],['check_auxiliary.py'],['audit/check_second_assembly_fast.py']]
for job in jobs:
    print('Running',*job,flush=True)
    subprocess.run([sys.executable,'-O',*job],cwd=root/'checks',check=True)
record={'passed':True,'jobs':[j[0] for j in jobs],'seconds':time.time()-start}
(root/'check_receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print('All exact checks passed',flush=True)
