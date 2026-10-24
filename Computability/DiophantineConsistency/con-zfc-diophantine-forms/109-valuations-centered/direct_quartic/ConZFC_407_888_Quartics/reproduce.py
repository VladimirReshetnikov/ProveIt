#!/usr/bin/env python3
"""Rebuild the complete finite coefficient data, using only Python's standard library."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,sys

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import build_projected

def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,sort_keys=True,separators=(',',':'))+'\n')

def raw_record(b,label,local):
    return {'variables':b.variables,'rows':b.rows,
            'powers':[{'base':n,'exponent':k,'output':v} for (n,k),v in b.powers.items()],
            'factorials':[{'input':n,'output':v} for n,v in b.factorials.items()],
            'binomials':[{'n':n,'k':k,'output':v} for (n,k),v in b.binomials.items()],
            'ranges':b.range_requests,'radix':b.radix_data,'scale':b.shared_parameters,
            'auxiliary':b.common_index_parameters,'discriminant':b.pell_D,
            'derivations':b.index_derivations,
            'seeds':[{'exponent':k,'pair':v} for k,v in b.seed_indices.items()],
            'indices':[{'exponent':k,'pair':v} for k,v in b.shared_indices.items()],
            'label_majorant':label,'local_majorant':local}

def source_data():
    b,src,label,local=build_projected.construct()
    eq,poly,metrics=b.export(hashlib.sha256(src).hexdigest(),'projected_eight_columns',True)
    return b,eq,poly,metrics,raw_record(b,label,local)

def source_files(b,eq,poly,metrics,raw):
    return {
        'equation.json':eq,'expanded_polynomial.json':poly,
        'label_majorant.json':raw['label_majorant'],
        'local_majorant.json':raw['local_majorant'],
        'radix_certificate.json':b.radix_data,
        'macro_inventory.json':b.macro_log,
        'index_derivations.json':b.index_derivations,
        'gate_ledger.json':{'square_difference_gates':b.sqd_ledger,
                           'all_variables':b.variables,'all_rows':b.rows,'gates':b.gates},
        'METRICS.json':{'source':metrics,
                        'label_exponent':raw['label_majorant']['carrier_exponent'],
                        'local_exponent':raw['local_majorant']['emitted_exponent'],
                        'seed_indices':len(b.seed_indices)}}

def run(command):
    result=subprocess.run(command,text=True,capture_output=True)
    if result.returncode:
        raise RuntimeError('Subprocess failed: '+result.stdout+result.stderr)
    return result.stdout

def generate(output):
    output=Path(output).resolve()
    if output.exists() and any(output.iterdir()):raise ValueError('output directory must be empty')
    output.mkdir(parents=True,exist_ok=True)
    b,eq,poly,metrics,raw=source_data()
    source=output/'source690';source.mkdir()
    for name,value in source_files(b,eq,poly,metrics,raw).items():write(source/name,value)
    write(source/'raw_audit_input.json',raw)
    prefix=[sys.executable]+([] if __debug__ else ['-O'])
    for name,cap in [('natural407',64),('natural410',16)]:
        run(prefix+[str(ROOT/'code/psd_contract/contract.py'),str(source/'equation.json'),
                    str(output/name),'--support-cap',str(cap)])
    for name,cap in [('integer888',16),('integer917',4)]:
        run(prefix+[str(ROOT/'code/integer_pipeline/build_integer.py'),'--source',
                    str(source/'equation.json'),'--output',str(output/name),'--max-support',str(cap)])
    return {'status':'PASS','source_variables':metrics['variables'],
            'output':str(output),'equations':['natural407','natural410','integer888','integer917']}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();print(json.dumps(generate(a.output),indent=2))
