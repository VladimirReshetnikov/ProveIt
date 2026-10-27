"""Recheck an extracted release. No network, benchmark retiming or Lean build."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,zipfile

SCRIPTS=['matrix_checks/verify_rectangular_tree.py','matrix_checks/verify_four_plan.py',
         'matrix_checks/verify_degree_051_cached.py','tree_checks/check_schedule_combinations.py',
         'tree_checks/check_matching_factorized.py','tree_checks/audit_four_plan.py',
         'code/check_mixed_projective.py','qa/check_components_independent.py',
         'qa/check_degree051_independent.py']

def main(archive,output):
    archive=Path(archive).resolve();records=[]
    with tempfile.TemporaryDirectory(prefix='eth3-replay-') as name:
        tmp=Path(name)
        with zipfile.ZipFile(archive) as z:
            if sum(i.file_size for i in z.infolist())>64*1024*1024:raise ValueError('release size limit')
            for n in z.namelist():
                if not (tmp/n).resolve().is_relative_to(tmp):raise ValueError('unsafe ZIP path')
            if z.testzip():raise ValueError('bad CRC')
            z.extractall(tmp)
        root=tmp/'eth_iteration3'
        def run(args,fail=False):
            p=subprocess.run([sys.executable,'-B']+args,cwd=root,text=True,capture_output=True)
            records.append({'args':args,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
            if (p.returncode==0)==fail:raise RuntimeError(records[-1])
        run(['code/verify_bundle.py'])
        for opt in ([],['-O']):
            for script in SCRIPTS:run(opt+[script])
        run(['code/verify_bundle.py'])
        f=root/'README.txt';old=f.read_bytes();f.write_bytes(old+b'\nchanged\n');run(['code/verify_bundle.py'],True);f.write_bytes(old)
        f.rename(root/'README.missing');run(['code/verify_bundle.py'],True);(root/'README.missing').rename(f)
        f=root/'anthropic_snapshot/eth/MainResults.lean';old=f.read_bytes();s=root/'SHA256SUMS';olds=s.read_text()
        f.write_bytes(old+b'\n')
        s.write_text('\n'.join((hashlib.sha256(f.read_bytes()).hexdigest()+'  '+str(f.relative_to(root))) if l.endswith('  '+str(f.relative_to(root))) else l for l in olds.splitlines())+'\n')
        run(['code/verify_bundle.py'],True);f.write_bytes(old);s.write_text(olds)
        run(['code/verify_bundle.py'])
    result={'success':True,'archive':archive.name,'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
            'positive_stages':21,'negative_integrity_controls':3,'records':records,
            'scope':'Authored exact finite checks and stored-source integrity, not an independent Lean build or full SAT validation. Timings are not rerun.'}
    Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
if __name__=='__main__':
    if len(sys.argv)!=3:raise SystemExit('usage: replay_archive.py RELEASE.zip OUTPUT.json')
    main(sys.argv[1],sys.argv[2])
