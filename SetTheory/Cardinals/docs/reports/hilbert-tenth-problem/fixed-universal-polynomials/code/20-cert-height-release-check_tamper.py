#!/usr/bin/env python3
"""Negative controls for the independently authored height checker only.
Subprocess execution is restricted to copied height_check.py. All upstream
snapshots are inert files, including the snapshot whose suffix is .py.
"""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
CASES=[
 ('source_python_pin','source/complete82_auxiliary_square_product_chart.py',None,'\n# altered data snapshot\n','data pin source/complete82_auxiliary_square_product_chart.py'),
 ('source_json_pin','source/complete82_auxiliary_square_product_chart.json',None,'\n','data pin source/complete82_auxiliary_square_product_chart.json'),
 ('recovered_proof_pin','BASE_COUNTERFAMILY.md',None,'\n','data pin BASE_COUNTERFAMILY.md'),
 ('wrong_tau_floor','height_check.py',"exact_bl(tau,p*L,'tau')","exact_bl(tau,p*L+1,'tau')",'tau exact bit length'),
 ('wrong_auxiliary_floor','height_check.py',"exact_bl(yaux,N+1,'yaux')","exact_bl(yaux,N,'yaux')",'yaux exact bit length'),
 ('wrong_U_floor','height_check.py',"exact_bl(U,N-C+1,'U')","exact_bl(U,N-C+2,'U')",'U exact bit length'),
 ('hard_cap','height_check.py','CAP = 500_000','CAP = 1_000','prospective component cap'),
]

def need(ok,message):
    if not ok:raise ValueError(message)

def run():
    records=[]
    for label,name,old,new,error in CASES:
        with tempfile.TemporaryDirectory(prefix='height-independent-negative-') as td:
            target=Path(td)
            shutil.copy2(ROOT/'height_check.py',target/'height_check.py')
            shutil.copy2(ROOT/'BASE_COUNTERFAMILY.md',target/'BASE_COUNTERFAMILY.md')
            shutil.copytree(ROOT/'source',target/'source')
            p=target/name; text=p.read_text()
            if old is None:text+=new
            else:
                need(text.count(old)==1,'unique tamper site '+label)
                text=text.replace(old,new,1)
            p.write_text(text)
            for optimized in [False,True]:
                command=[sys.executable]+(['-O'] if optimized else [])+[str(target/'height_check.py')]
                result=subprocess.run(command,capture_output=True,text=True,timeout=30)
                need(result.returncode!=0,'tamper accepted '+label)
                need(error in result.stderr,'wrong tamper failure '+label)
                records.append({'case':label,'optimized':optimized,'rejected':True,'expected_error':error})
    return {'status':'PASS','scope':'Negative controls execute only fresh copied author height checker; source files remain data.','rejected_cases':records}

if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
