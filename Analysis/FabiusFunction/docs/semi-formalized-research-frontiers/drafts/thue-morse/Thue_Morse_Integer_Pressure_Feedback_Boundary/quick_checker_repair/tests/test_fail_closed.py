#!/usr/bin/env python3
"""Failure-injection tests use disposable symlink fixtures; sealed inputs are read-only."""
from pathlib import Path
import argparse,ast,json,os,shutil,subprocess,sys,tempfile,hashlib
ROOT=Path(__file__).resolve().parents[1]

def require(c,m):
    if not c:raise RuntimeError(m)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--data-dir',type=Path,required=True)
    args=p.parse_args();source=args.data_dir.resolve()
    manifest=json.loads((ROOT/'input_manifest.json').read_text())['certificate_sha256']
    before={rel:hashlib.sha256((source/rel).read_bytes()).hexdigest() for rel in manifest}
    require(before==manifest,'Original dataset must match sealed input manifest before testing')
    names=['verify_cutoff.py','check_trace_coverage.py','check_m2_response.py','check_m2_pressure.py']
    for name in names:
        tree=ast.parse((ROOT/'code'/name).read_text())
        require(not any(isinstance(n,ast.Assert) for n in ast.walk(tree)),'Optimization-sensitive assert remains in '+name)
    records=[]
    with tempfile.TemporaryDirectory(prefix='feedback_repair_tests_') as temp:
        base=Path(temp)
        fixtures={}
        for scenario in ['complete','missing_one_trace','missing_all_traces','corrupt_json','corrupt_trace']:
            data=base/scenario/'data';(data/'certificates').mkdir(parents=True)
            for rel in manifest:
                if scenario=='missing_one_trace' and rel=='certificates/parity_m002.json.trace.gz':continue
                if scenario=='missing_all_traces' and rel.endswith('.trace.gz'):continue
                dest=data/rel
                if scenario=='corrupt_json' and rel=='certificates/parity_m002.json':
                    z=json.loads((source/rel).read_text());z['H_lower_numerator']=str(int(z['H_lower_numerator'])+1)
                    dest.write_text(json.dumps(z))
                elif scenario=='corrupt_trace' and rel=='certificates/parity_m002.json.trace.gz':
                    content=(source/rel).read_bytes();dest.write_bytes(content[:-1]+bytes([content[-1]^1]))
                else:dest.symlink_to(source/rel)
            fixtures[scenario]=data
        for mode in ['normal','python_O','PYTHONOPTIMIZE_1']:
            env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None)
            flags=[]
            if mode=='python_O':flags=['-O']
            if mode=='PYTHONOPTIMIZE_1':env['PYTHONOPTIMIZE']='1'
            for scenario,data in fixtures.items():
                for entry in ['check_trace_coverage.py','run_all.py']:
                    output=base/'outputs'/mode/scenario/entry
                    cmd=[sys.executable,*flags,str(ROOT/'code'/entry),'--data-dir',str(data),'--output-dir',str(output)]
                    run=subprocess.run(cmd,env=env,capture_output=True,text=True)
                    should_pass=scenario=='complete'
                    require((run.returncode==0)==should_pass,f'Unexpected exit: {mode}, {scenario}, {entry}: {run.returncode}\n{run.stderr}')
                    check=json.loads((output/'trace_checks.json').read_text())
                    require(check['complete']==should_pass,'Misleading complete flag')
                    if should_pass:require(check['certified_moments']==68 and check['checked_response_orders']==4828,'Coverage mismatch')
                    else:require('All four repaired quick checks passed' not in run.stdout,'False success text')
                    if entry=='run_all.py':
                        summary=json.loads((output/'run_summary.json').read_text())
                        require(summary['all_checks_passed']==should_pass,'Misleading runner summary')
                        require(summary['optimization']==(0 if mode=='normal' else 1),'Optimization flag lost')
                        if should_pass:
                            for cert in ['cutoff_certificate.json','m2_response_certificate.json','m2_negative_higher_certificate.json']:
                                require(json.loads((output/cert).read_text())==json.loads((source/cert).read_text()),'Exact mathematics changed: '+cert)
                    records.append({'mode':mode,'scenario':scenario,'entry':entry,'exit_code':run.returncode,'expected_success':should_pass})
            # Replace one original require condition by False in each checker, to prove
            # that a mathematical acceptance test remains active under optimization.
            for name in names:
                mutation=base/'mutation'/mode/name; (mutation/'code').mkdir(parents=True)
                shutil.copy2(ROOT/'code'/'repair_common.py',mutation/'code'/'repair_common.py')
                shutil.copy2(ROOT/'input_manifest.json',mutation/'input_manifest.json')
                tree=ast.parse((ROOT/'code'/name).read_text())
                class InjectFailure(ast.NodeTransformer):
                    changed=False
                    def visit_Call(self,node):
                        if not self.changed and isinstance(node.func,ast.Name) and node.func.id=='require':
                            node.args[0]=ast.Constant(False);self.changed=True
                        return self.generic_visit(node)
                transform=InjectFailure();tree=transform.visit(tree);require(transform.changed,'No acceptance check found')
                target=mutation/'code'/name;target.write_text(ast.unparse(ast.fix_missing_locations(tree))+'\n')
                run=subprocess.run([sys.executable,*flags,str(target),'--data-dir',str(source),'--output-dir',str(mutation/'output')],env=env,capture_output=True,text=True)
                require(run.returncode!=0,f'Acceptance disabled under {mode}: {name}')
                require('VerificationError' in run.stderr,f'Wrong failure path under {mode}: {name}')
                records.append({'mode':mode,'scenario':'injected_false_acceptance','entry':name,'exit_code':run.returncode,'expected_success':False})
    after={rel:hashlib.sha256((source/rel).read_bytes()).hexdigest() for rel in manifest}
    require(before==after,'Sealed input dataset was modified')
    out={'status':'PASS','tests':len(records),'sealed_inputs_unchanged':True,'original_exact_output_certificates_unchanged':True,'assert_nodes_in_four_checkers':0,'records':records}
    (ROOT/'results'/'failure_injection_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(f'PASS: {len(records)} complete/missing/corrupt/mathematical-failure tests across normal, -O, and PYTHONOPTIMIZE=1')

if __name__=='__main__':main()
