#!/usr/bin/env python3
"""Require rejection of corrupt domain proofs and gate metadata."""
from pathlib import Path
from copy import deepcopy
import json,subprocess,sys,tempfile,argparse
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
    cert=json.loads((ROOT/'DOMAIN_CERTIFICATE.json').read_text())
    raw=json.loads((ROOT/'RAW_FRAME_INTERFACE.json').read_text())
    controls=[]
    bad=deepcopy(raw);bad['gates'][0]['left']=['c',97]
    controls.append(('changed_gate_operand',cert,bad,'gate metadata disagrees'))
    bad=deepcopy(cert);bad['guards']=bad['guards'][1:]
    controls.append(('deleted_nonnegative_guard',bad,raw,'sign'))
    bad=deepcopy(cert)
    row=next(s for s in bad['pre_steps'] if s['row'] is not None)
    row['sign']*=-1
    controls.append(('reversed_pivot_orientation',bad,raw,'positive'))
    bad=deepcopy(cert);bad['frame_conclusions']=bad['frame_conclusions'][1:]
    controls.append(('omitted_frame_conclusion',bad,raw,'frame conclusions differ'))
    bad=deepcopy(raw);bad['frame']['bases'][0]['row']=bad['frame']['norm_row']
    controls.append(('wrong_modulus_identity',cert,bad,'modulus defining identity'))
    results=[]
    with tempfile.TemporaryDirectory(prefix='projected-domain-negative-') as td:
        td=Path(td)
        for name,c,r,expected in controls:
            cp=td/(name+'.cert.json');rp=td/(name+'.raw.json')
            cp.write_text(json.dumps(c));rp.write_text(json.dumps(r))
            cmd=[sys.executable]+([] if __debug__ else ['-O'])+[str(HERE/'check_domain_certificate.py'),
                 '--certificate',str(cp),'--raw-interface',str(rp)]
            run=subprocess.run(cmd,text=True,capture_output=True)
            if run.returncode==0 or expected not in run.stderr:
                raise ValueError('corruption not rejected for intended reason: '+name+' '+run.stderr[-500:])
            results.append({'case':name,'rejected':True,'expected_failure_fragment':expected})
    result={'status':'PASS','controls':results,'optimized_python':not __debug__}
    if args.output:args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
