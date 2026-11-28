"""Audit against a local Git checkout containing the pinned commit. No network."""
import csv, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parent
repo=sys.argv[1]
commit='9050b04000647d588d0c78d945180abcd3b0bcf7'
prefix='Analysis/GeneralizedRiemannHypothesis/'
def git(*args):
    return subprocess.check_output(['git','-C',repo,*args],text=True).strip()
for filename,field,sha_field,subdir in [('source_audit.tsv','path','blob_sha',''),('proposal_audit.tsv','directory','tree_sha','docs/proposals/')]:
    with (root/filename).open() as f:
        rows=list(csv.DictReader(f,delimiter='\t'))
    for row in rows:
        path=prefix+subdir+row[field]
        actual=git('rev-parse',commit+':'+path)
        assert actual==row[sha_field],(path,actual,row[sha_field])
    print(f'{filename}: {len(rows)} object identities verified')
