#!/usr/bin/env python3
"""Check the literal equations, proof deltas, restorations, and coefficient data.

Finite verification does not decide consistency or replace the supplied
unbounded proofs and identified logical calibration.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import check_pipeline,check_affine,finite_controls,audit_changed_source
from check_new_arithmetic import check_lcm,check_binomial_selectors,check_odd_binomials,check_label_coefficients_and_injectivity
PROFILES=('P238','P239_sparse','P239_low_height')
def require(condition,message):
    if not condition:raise ValueError(message)
def verify(rebuild=False,skip_manifest=False):
    manifest_path=ROOT/'MANIFEST.sha256.json'
    if not skip_manifest and manifest_path.exists():
        for name,digest in json.loads(manifest_path.read_text()).items():
            require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,'Manifest mismatch: '+name)
    parent=ROOT/'inherited/factorial_free/direct/factorial_free_affine/raw_source.json'
    result=check_pipeline.check(parent,ROOT/'source',[ROOT/'equations'/n for n in PROFILES])
    result['separate_frame_audit']=audit_changed_source.audit(parent,ROOT/'source/raw_source.json')
    result['negative_controls']=finite_controls.run(parent,ROOT/'source')
    result['arithmetic_sanity']={'lcm':check_lcm(),'CRT':check_binomial_selectors(),
        'parity_beta':check_odd_binomials(),'label_separation':check_label_coefficients_and_injectivity()}
    comparisons={}
    for path in sorted((ROOT/'comparisons').glob('*/equation.json')):
        equation=json.loads(path.read_text());rows=[check_affine.decode(r['terms']) for r in equation['residuals']]
        metrics,poly=check_pipeline.metrics(rows,len(equation['variables']))
        comparisons[path.parent.name]=metrics
        stated_path=path.parent/'METRICS.json'
        if stated_path.exists():
            stated=json.loads(stated_path.read_text())
            for key in ('variables','rows','degree','monomials','height'):
                if key in stated:require(stated[key]==metrics[key],'Comparison metric '+key)
    result['recollected_comparisons']=comparisons
    if (ROOT/'report/report.tex').exists():
        import build_report
        build_report.check_generated()
        result['report_specification']='All generated residuals and metrics match the literal equation data'
    if rebuild:
        with tempfile.TemporaryDirectory(prefix='conzfc_linear_rebuild_') as tmp:
            tmp=Path(tmp);stage=tmp/'source'
            command=[sys.executable,'-B']+(['-O'] if not __debug__ else [])
            subprocess.run(command+[str(ROOT/'code/build_source.py'),'--output',str(stage),'--minimal-growth'],check=True,capture_output=True,text=True)
            regenerated=[]
            for path in sorted((ROOT/'source').glob('*.json')):
                require(path.read_bytes()==(stage/path.name).read_bytes(),'Source rebuild mismatch '+path.name)
                regenerated.append('source/'+path.name)
            subprocess.run(command+[str(ROOT/'code/replay_endpoints.py'),str(tmp/'equations'),'--stage',str(stage)],check=True,capture_output=True,text=True)
            for profile in PROFILES:
                for name in ('equation.json','expanded_polynomial.json','METRICS.json'):
                    target=ROOT/'equations'/profile/name;built=tmp/'equations'/profile/name
                    require(target.read_bytes()==built.read_bytes(),'Endpoint rebuild mismatch '+profile+'/'+name)
                    regenerated.append('equations/'+profile+'/'+name)
            result['byte_identical_rebuild']=regenerated
    result['status']='PASS'
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--rebuild',action='store_true');p.add_argument('--skip-manifest',action='store_true');p.add_argument('--receipt',type=Path)
    args=p.parse_args();result=verify(args.rebuild,args.skip_manifest);data=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(data)
    print(json.dumps({'status':result['status'],'profiles':list(PROFILES),'rebuild_files':len(result.get('byte_identical_rebuild',[])),
        'comparison_metrics':result['recollected_comparisons'],'scope':'Finite algebra plus supplementary arithmetic regressions; ordinary proof supplied separately'},indent=2))
