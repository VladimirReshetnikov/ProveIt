#!/usr/bin/env python3
"""Fresh release tests. Executes only the inspected replay adapter/owned checker.
Every destructive case changes disposable copies, never the frozen inputs.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def require(condition,message):
    if not condition:raise RuntimeError(message)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--science-root',required=True)
    ap.add_argument('--audit-root',required=True)
    ap.add_argument('--results',required=True)
    args=ap.parse_args()
    base=Path(__file__).resolve().parent
    adapter=base/'replay.py';pins=base/'PINNED_INPUTS.json'
    science=Path(args.science_root);audit=Path(args.audit_root)
    spec=importlib.util.spec_from_file_location('release62_adapter',adapter)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    pin_data=json.loads(pins.read_text())
    original_science,_=module.inventory(science,pin_data['roots']['science'])
    original_audit,_=module.inventory(audit,pin_data['roots']['audit'])
    root=Path(tempfile.mkdtemp(prefix='release62-replay-tests-'))
    records=[]
    def case(name,edit=None,expected=True,optimize=False):
        folder=root/name;folder.mkdir()
        s=folder/'science';a=folder/'audit';p=folder/'pins.json';o=folder/'output'
        shutil.copytree(science,s,copy_function=shutil.copy2)
        shutil.copytree(audit,a,copy_function=shutil.copy2)
        shutil.copy2(pins,p)
        config={'science':str(s),'audit':str(a),'pins':str(p),'output':str(o)}
        if edit:edit(s,a,p,o,config)
        cmd=[sys.executable,'-I','-B']+(['-O'] if optimize else [])+[str(adapter),'--science-root',config['science'],'--audit-root',config['audit'],'--pins',config['pins'],'--output-root',config['output']]
        result=subprocess.run(cmd,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=root,
                              env={'PATH':os.defpath,'LANG':'C.UTF-8','LC_ALL':'C.UTF-8'},timeout=30)
        require((result.returncode==0)==expected,name+': unexpected result '+repr(result.stderr))
        if expected:
            receipt=json.loads((o/'replay_receipt.json').read_text())
            require(receipt['passed'] and receipt['checker_compile_optimize']==0,name+': bad receipt')
            for f in module.GOLDEN:
                require((o/'evidence'/f).read_bytes()==(audit/'evidence'/f).read_bytes(),name+': golden mismatch '+f)
            require((o/'execution_stdout.json').read_bytes()==(audit/'evidence/run_stdout.json').read_bytes(),name+': stdout mismatch')
            require((o/'evidence/frozen_before.json').read_bytes()==(o/'evidence/frozen_after.json').read_bytes(),name+': transport snapshot mismatch')
        else:
            require(b'REJECTED:' in result.stderr,name+': rejection missing')
        records.append({'test':name,'passed':True,'expected_success':expected,'python_optimize':optimize,'returncode':result.returncode,'diagnostic':result.stderr.decode().strip()})
    def mutate(rel,which='science'):
        def edit(s,a,p,o,c):
            f=(s if which=='science' else a)/rel
            f.write_bytes(f.read_bytes()+b'\nTAMPER\n')
        return edit
    case('relocated_success')
    case('optimized_python_success',optimize=True)
    def readonly(s,a,p,o,c):
        for r in (s,a):
            for f in r.rglob('*'):
                f.chmod(0o555 if f.is_dir() else 0o444)
            r.chmod(0o555)
        p.chmod(0o444)
    case('readonly_relocation_success',readonly)
    case('readonly_optimized_success',readonly,optimize=True)
    for name,rel in [('proof','PROOF.md'),('author_source','static_algebra.py'),('rules','RULES44.json'),('positive_dependency','dependencies/positive_planar_PROOF.md'),('invertibility_dependency','dependencies/invertibility_GL2_PROOF.md')]:
        case('reject_science_tamper_'+name,mutate(rel),False)
    for name,rel in [('checker',module.CHECKER),('review','REVIEW.md'),('golden','evidence/independent_checks.json'),('old_snapshot','evidence/frozen_before.json'),('audit_manifest','AUDIT_MANIFEST.json')]:
        case('reject_audit_tamper_'+name,mutate(rel,'audit'),False)
    case('reject_extra_science_file',lambda s,a,p,o,c:(s/'extra.txt').write_text('x'),False)
    case('reject_extra_science_directory',lambda s,a,p,o,c:(s/'extra').mkdir(),False)
    case('reject_missing_science_file',lambda s,a,p,o,c:(s/'README.md').unlink(),False)
    case('reject_extra_audit_file',lambda s,a,p,o,c:(a/'extra.txt').write_text('x'),False)
    case('reject_missing_audit_file',lambda s,a,p,o,c:(a/'SHA256SUMS.txt').unlink(),False)
    case('reject_existing_output',lambda s,a,p,o,c:o.mkdir(),False)
    case('reject_output_inside_science',lambda s,a,p,o,c:c.update(output=str(s/'new-output')),False)
    case('reject_output_inside_audit',lambda s,a,p,o,c:c.update(output=str(a/'new-output')),False)
    case('reject_output_inside_adapter',lambda s,a,p,o,c:c.update(output=str(base/'should-never-exist')),False)
    case('reject_input_root_overlap',lambda s,a,p,o,c:c.update(audit=str(s)),False)
    case('reject_relative_root',lambda s,a,p,o,c:c.update(science='science'),False)
    case('reject_dotdot_alias',lambda s,a,p,o,c:c.update(science=str(s)+'/../science'),False)
    case('reject_repeated_slash',lambda s,a,p,o,c:c.update(science=str(s.parent)+'//science'),False)
    case('reject_trailing_slash',lambda s,a,p,o,c:c.update(audit=str(a)+'/'),False)
    case('reject_malformed_pins',lambda s,a,p,o,c:p.write_text('{bad'),False)
    case('reject_changed_pin_hash',lambda s,a,p,o,c:p.write_bytes(p.read_bytes()+b' '),False)
    def link_file(s,a,p,o,c):
        f=s/'README.md';f.unlink();f.symlink_to(science/'README.md')
    case('reject_symlink_file',link_file,False)
    def link_dir(s,a,p,o,c):
        shutil.rmtree(s/'dependencies');(s/'dependencies').symlink_to(science/'dependencies',target_is_directory=True)
    case('reject_symlink_directory',link_dir,False)
    def link_root(s,a,p,o,c):
        link=s.parent/'link';link.symlink_to(s,target_is_directory=True);c['science']=str(link)
    case('reject_symlink_root',link_root,False)
    def hardlink(s,a,p,o,c):
        f=s/'README.md';other=s.parent/'alias';os.link(f,other)
    case('reject_hardlink_alias',hardlink,False)
    def fifo(s,a,p,o,c):
        f=s/'README.md';f.unlink();os.mkfifo(f)
    case('reject_nonregular_input',fifo,False)
    # Direct schema tests exercise malformed pins that an authenticated CLI
    # already refuses at its outer digest gate. No checker executes in these.
    malformed=[]
    p=copy.deepcopy(pin_data);p['format']=True;malformed.append(('boolean_format',p))
    p=copy.deepcopy(pin_data);p['roots']['science']['files']['PROOF.md']['bytes']=True;malformed.append(('boolean_size',p))
    p=copy.deepcopy(pin_data);p['roots']['science']['files']['PROOF.md']['sha256']='A'*64;malformed.append(('uppercase_digest',p))
    p=copy.deepcopy(pin_data);p['roots']['science']['directories'].append('.');malformed.append(('duplicate_dir',p))
    p=copy.deepcopy(pin_data);p['roots']['science']['files']['../escape']=p['roots']['science']['files'].pop('PROOF.md');malformed.append(('relative_escape',p))
    p=copy.deepcopy(pin_data);p['roots']['science']['directories'].remove('dependencies');malformed.append(('missing_parent',p))
    for name,p in malformed:
        try:module.validate_pins(p)
        except module.Rejected:records.append({'test':'schema_'+name,'passed':True,'expected_success':False})
        else:raise RuntimeError('malformed schema accepted: '+name)
    try:json.loads('{"format":1,"format":1}',object_pairs_hook=module.unique_pairs)
    except module.Rejected:records.append({'test':'schema_duplicate_json_key','passed':True,'expected_success':False})
    else:raise RuntimeError('duplicate JSON key accepted')
    require(module.inventory(science,pin_data['roots']['science'])[0]==original_science,'original science metadata changed')
    require(module.inventory(audit,pin_data['roots']['audit'])[0]==original_audit,'original audit metadata changed')
    result={'passed':True,'test_count':len(records),'adapter_sha256':hashlib.sha256(adapter.read_bytes()).hexdigest(),'pins_sha256':hashlib.sha256(pins.read_bytes()).hexdigest(),'checker_sha256':module.CHECKER_SHA256,'scratch_root':str(root),'original_science_and_audit_preserved':True,'tests':records,'limits':'Disposable-tree tests, trusted Python/SymPy and quiescent POSIX filesystem; no hostile-runtime or OS/network sandbox claim.'}
    Path(args.results).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'passed':True,'tests':len(records),'results':args.results}))

if __name__=='__main__':main()
