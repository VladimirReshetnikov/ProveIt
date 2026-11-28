"""Check observed Git object identities in a local checkout. No network needed."""
import argparse, csv, subprocess
from pathlib import Path
base = Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('repo',help='local ProveIt Git checkout')
p.add_argument('--rev',default='HEAD',help='commit to compare with the observed main-branch blobs')
a=p.parse_args()
# Do not equate a separately reported head with the observed directory snapshot.
prefix='Analysis/GeneralizedRiemannHypothesis/'
items=[]
with (base/'source_anchors.tsv').open() as f:
    for row in csv.DictReader(f,delimiter='\t'):
        items.append((row['path'],row['blob_sha1']))
with (base/'proposal_audit.tsv').open() as f:
    for row in csv.DictReader(f,delimiter='\t'):
        items.append(('docs/proposals/'+row['directory'],row['tree_sha1']))
bad=0
for path,want in items:
    r=subprocess.run(['git','-C',a.repo,'rev-parse','--verify',f'{a.rev}:{prefix}{path}'],capture_output=True,text=True)
    got=r.stdout.strip() if r.returncode==0 else '(missing)'
    if want!=got:
        print(f'MISMATCH {path}: expected {want}, got {got}');bad+=1
print(f'{len(items)-bad}/{len(items)} identities matched; {bad} mismatches')
raise SystemExit(bool(bad))
