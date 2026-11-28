#!/usr/bin/env python3
import argparse,csv,subprocess,pathlib
p=argparse.ArgumentParser();p.add_argument('repo');p.add_argument('--rev',default='main');a=p.parse_args()
root=pathlib.Path(__file__).resolve().parent
base='Analysis/GeneralizedRiemannHypothesis/'
counts={'match':0,'mismatch':0,'unavailable':0}
for table,prefix in [('source_anchors.tsv',base),('proposal_audit.tsv',base+'docs/proposals/')]:
    with (root/table).open() as f:
        for path,expected,_ in list(csv.reader(f,delimiter='\t'))[1:]:
            if expected=='UNAVAILABLE':counts['unavailable']+=1;continue
            r=subprocess.run(['git','-C',a.repo,'rev-parse',f'{a.rev}:{prefix}{path}'],capture_output=True,text=True)
            status='match' if r.returncode==0 and r.stdout.strip()==expected else 'mismatch'
            counts[status]+=1
            if status=='mismatch':print(path,expected,r.stdout.strip() or 'not found')
print(counts)
raise SystemExit(bool(counts['mismatch']))
