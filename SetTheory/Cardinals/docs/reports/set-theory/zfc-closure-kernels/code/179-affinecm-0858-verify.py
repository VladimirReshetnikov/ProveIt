#!/usr/bin/env python3
"""Fast finite audit by default; optional full symbolic CI rerun."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--universal',action='store_true',help='Also recheck all1900 arbitrary-value CI contracts, about90 seconds.');a=ap.parse_args();root=Path(__file__).resolve().parent;beg=time.time()
    bindings=json.loads((root/'current-bindings.json').read_text())
    assert not bindings['differing_or_missing_files']
    for row in bindings['files']:
        raw=(root/row['local_path']).read_bytes()
        assert hashlib.sha256(raw).hexdigest()==row['sha256']
        blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        assert blob==row['git_blob']==row['current_tree_blob']
    assert bindings['matched_files']==len(bindings['files'])
    print('CURRENT_PIN_REFERENCE_BINDINGS_PASS',len(bindings['files']),flush=True)
    commands=[
      ['audit_window_invariant.py','k215.tm','k215_window5.json'],
      ['audit_spare_counterexamples.py','k215.tm','existential_spare_refined.json','existential_spare_timeout_resolution.json'],
      ['bind_noappend_result.py'],
      ['check_noappend_obstruction.py']]
    if a.universal:
        commands.insert(2,['symbolic_noappend_increment.py','--candidate-root','reference/k215'])
    for cmd in commands:
        print('RUN',' '.join(cmd),flush=True);subprocess.run([sys.executable,*cmd],cwd=root,check=True)
    result={'status':'PASS','finite_checks':4,'current_pin_reference_bindings':len(bindings['files']),'universal_CI_rerun':a.universal,'seconds':time.time()-beg,'claim':'Finite audits pass. No correct214-state consistency machine is claimed.'}
    (root/'verification_summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
