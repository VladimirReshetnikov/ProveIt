#!/usr/bin/env python3
"""Clean-copy, -O, schema, semantic-mutation and output-refusal tests."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[1]
class TestFailure(Exception):pass

def need(condition,message):
    if not condition:raise TestFailure(message)

def snapshot(root):
    answer={}
    for path in sorted(root.rglob('*')):
        need(not path.is_symlink(),'symlink in source tree')
        if path.is_file():answer[path.relative_to(root).as_posix()]=hashlib.sha256(path.read_bytes()).hexdigest()
    return answer

def make_copy(parent,name):
    dest=parent/name;dest.mkdir()
    for name in ('checks','data'):shutil.copytree(ROOT/name,dest/name)
    return dest

def freeze(root):
    for path in root.rglob('*'):
        path.chmod(0o555 if path.is_dir() else 0o444)
    root.chmod(0o555)

def thaw(root):
    if root.exists():
        root.chmod(0o755)
        for path in root.rglob('*'):
            if path.is_dir():path.chmod(0o755)
            else:path.chmod(0o644)

def invoke(source,optimized=False,output=None):
    command=[sys.executable]
    if optimized:command.append('-O')
    command.append(str(source/'checks/check_exact.py'))
    if output is not None:command.extend(['--output',str(output)])
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run(command,cwd=source.parent,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=240,check=False)

def json_change(source,file,update):
    path=source/'data'/file;obj=json.loads(path.read_text());update(obj)
    path.write_text(json.dumps(obj,sort_keys=True,indent=2)+'\n')

def code_change(source,old,new):
    path=source/'checks/check_exact.py';text=path.read_text()
    need(text.count(old)==1,'mutation anchor is not unique: '+old)
    path.write_text(text.replace(old,new))

def mutations():
    return [
      ('semantic_distribution',lambda s:json_change(s,'expected.json',lambda x:x['diagonal_distributions']['4'].__setitem__(2,13)),'independent DSASM diagonal enumeration'),
      ('semantic_cumulant',lambda s:json_change(s,'expected.json',lambda x:x['pressure_cumulants'].__setitem__('3','1/27')),'pressure cumulant fixture'),
      ('schema_extra_key',lambda s:json_change(s,'cases.json',lambda x:x.__setitem__('unexpected',True)),'cases has wrong key inventory'),
      ('schema_missing_key',lambda s:json_change(s,'expected.json',lambda x:x['diagonal_distributions'].pop('3')),'diagonal distributions has wrong key inventory'),
      ('schema_bool_integer',lambda s:json_change(s,'expected.json',lambda x:x['diagonal_distributions']['1'].__setitem__(1,True)),'distribution entries must be nonnegative integers'),
      ('schema_noncanonical_fraction',lambda s:json_change(s,'expected.json',lambda x:x['pressure_cumulants'].__setitem__('1','2/6')),'noncanonical rational fixture'),
      ('schema_range_change',lambda s:json_change(s,'cases.json',lambda x:x.__setitem__('boundary_n_max',7)),'invalid or altered case declaration: boundary_n_max'),
      ('schema_duplicate_key',lambda s:(s/'data/cases.json').write_text((s/'data/cases.json').read_text().replace('"boundary_n_max": 8,','"boundary_n_max": 8, "boundary_n_max": 8,')),'duplicate JSON key: boundary_n_max'),
      ('closed_inventory_extra',lambda s:(s/'data/unlisted.json').write_text('{}\n'),'closed data inventory'),
      ('semantic_christoffel_factor',lambda s:code_change(s,'36*(2*n+1)*(2*n+3))','72*(2*n+1)*(2*n+3))'),'Christoffel divisibility'),
      ('semantic_source_pole',lambda s:code_change(s,'H*F(t+1,4)*e**2','H*F(t+2,4)*e**2'),'source density removable pole numerator'),
      ('semantic_basis_phase',lambda s:code_change(s,'pscale(jp,I**n*factorial(n+1))','pscale(jp,(-I)**n*factorial(n+1))'),'negative-leading basis phase i^n'),
      ('semantic_adjoint_order',lambda s:code_change(s,'adjoint_compression=mm(tr,weighted)','adjoint_compression=mm(weighted,tr)'),'finite Hahn adjoint resolvent ordering'),
      ('semantic_defect_sign',lambda s:code_change(s,'rhs=vsub(mv([r[:n] for r in bt[:n]],defect),mv(bt,tail)[:n])','rhs=[x+y for x,y in zip(mv([r[:n] for r in bt[:n]],defect),mv(bt,tail)[:n])]'),'finite-section exact defect recurrence with adjoint'),
      ('semantic_amplitude_power',lambda s:code_change(s,'amplitude4=s*s/(3*p)','amplitude4=s*s/(3*p*p)'),'fourth-power amplitude factor at s=1'),
    ]

def execute():
    records=[]; baseline=[];copies=[]
    original=snapshot(ROOT/'checks')|{'data/'+k:v for k,v in snapshot(ROOT/'data').items()}
    with tempfile.TemporaryDirectory(prefix='report128-exact-audit-') as folder:
        temp=Path(folder)
        try:
            for optimized in (False,True):
                source=make_copy(temp,'baseline_optimized' if optimized else 'baseline_normal');copies.append(source)
                freeze(source);before=snapshot(source)
                output=temp/('optimized.json' if optimized else 'normal.json')
                run=invoke(source,optimized,output)
                need(run.returncode==0,'baseline failed: '+run.stderr.decode())
                need(output.is_file(),'baseline output missing')
                need(snapshot(source)==before,'clean-copy baseline altered source')
                payload=output.read_bytes();result=json.loads(payload)
                need(result['status']=='PASS' and result['infinite_limits_certified'] is False,'baseline scope/status')
                need(set(result)=={'schema','status','arithmetic','infinite_limits_certified','boundary','hahn_christoffel','hahn_resolvent','basis_phase','source_algebra','finite_section','normalizations','input_sha256'},'result key inventory')
                baseline.append(payload)
                records.append({'test':'immutable_clean_copy','mode':'optimized' if optimized else 'normal','status':'PASS'})
                # Existing, in-source and symlinked output destinations all fail before arithmetic.
                for name,target,marker in [
                    ('existing_output',output,'refusing existing output target'),
                    ('source_output',source/'new-result.json','refusing output inside source package')]:
                    before_output=output.read_bytes()
                    refusal=invoke(source,optimized,target)
                    need(refusal.returncode!=0 and marker in refusal.stderr.decode(),name+' did not refuse')
                    need(output.read_bytes()==before_output,'existing output was modified')
                    need(snapshot(source)==before,'output refusal altered source')
                    records.append({'test':name,'mode':'optimized' if optimized else 'normal','status':'PASS'})
                link=temp/('link-o.json' if optimized else 'link.json');link.symlink_to(output)
                refusal=invoke(source,optimized,link)
                need(refusal.returncode!=0 and 'refusing existing output target' in refusal.stderr.decode(),'symlink output not refused')
                need(output.read_bytes()==payload,'symlink target altered')
                records.append({'test':'symlink_output','mode':'optimized' if optimized else 'normal','status':'PASS'})
            need(baseline[0]==baseline[1],'normal and -O output bytes differ')
            for name,mutation,marker in mutations():
                source=make_copy(temp,name);copies.append(source);mutation(source);freeze(source);before=snapshot(source)
                for optimized in (False,True):
                    run=invoke(source,optimized)
                    need(run.returncode!=0 and marker in run.stderr.decode(),name+' did not fail at expected guard: '+run.stderr.decode())
                    need(run.stdout==b'','failed mutant emitted success JSON')
                    need(snapshot(source)==before,'mutant execution altered source')
                    records.append({'test':name,'mode':'optimized' if optimized else 'normal','status':'PASS','expected_rejection':marker})
        finally:
            for source in copies:thaw(source)
    final=snapshot(ROOT/'checks')|{'data/'+k:v for k,v in snapshot(ROOT/'data').items()}
    need(final==original,'audit modified original companion files')
    return {'schema':'dsasm-report128-exact-audit-v1','status':'PASS','normal_optimized_byte_identical':True,'clean_copies_immutable':True,'result_sha256':hashlib.sha256(baseline[0]).hexdigest(),'cases':records,'scope':'Finite exact identities and selected adversarial cases only; this harness is not proof of any infinite-size limit.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path);args=parser.parse_args()
    try:
        if args.output:
            target=args.output.absolute()
            need(not target.exists() and not target.is_symlink(),'refusing existing output target')
            need(target.parent.is_dir(),'output parent must already exist')
            need(target==target.resolve(),'refusing noncanonical or symlinked output path')
            need(not target.resolve().is_relative_to(ROOT),'refusing output inside source package')
        result=execute();payload=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode()
        if args.output:
            with args.output.open('xb') as output:output.write(payload)
            print('PASS: '+str(len(result['cases']))+' audit cases; result SHA256 '+hashlib.sha256(payload).hexdigest())
        else:sys.stdout.buffer.write(payload)
        return 0
    except (TestFailure,OSError,ValueError,subprocess.TimeoutExpired) as exc:
        print('FAIL: '+str(exc),file=sys.stderr);return 1
if __name__=='__main__':raise SystemExit(main())
