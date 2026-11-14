#!/usr/bin/env python3
"""Compile and replay the two compact finite bootstrap experiments offline."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,tempfile
HERE=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=HERE/'replayed')
    args=p.parse_args()
    expected=json.loads((HERE/'receipt.json').read_text())
    assert hashlib.sha256((HERE/'runtime193.native.tm').read_bytes()).hexdigest()==expected['runtime193_sha256']
    args.output.mkdir(parents=True,exist_ok=True)
    results={}
    with tempfile.TemporaryDirectory(prefix='pa-bootstrap-')as tmp:
        for name in ('startup_pairs','permutation_bootstrap'):
            subprocess.run(['g++','-O3','-std=c++17',str(HERE/(name+'.cpp')),'-o',str(Path(tmp)/name)],check=True)
        jobs=[('pairs',[str(Path(tmp)/'startup_pairs'),str(HERE/'runtime193.native.tm'),str(HERE/'candidate_edits.tsv'),'1000000','0','99999',str(HERE/'all_source_frames.tsv')]),('permutations',[str(Path(tmp)/'permutation_bootstrap'),str(HERE/'runtime193.native.tm'),str(HERE/'safe_source_frames.tsv'),'200000'])]
        for name,command in jobs:
            run=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
            (args.output/(name+'.hits.jsonl')).write_text(run.stdout)
            (args.output/(name+'.log')).write_text(run.stderr)
            last=run.stderr.strip().splitlines()[-1]
            assert last.startswith('DONE ')and not run.stdout.strip(),(name,last)
            fields=dict(re.findall(r'(\w+) ([0-9]+)(?= |$)',last))
            counts={k:int(v)for k,v in fields.items()if k!='seconds'}
            if name=='pairs':
                assert all(counts[k]==v for k,v in {'edits':347,'successes':0,'simulations':471684,'ticks':586554596,'halts':117967,'rays':353129,'limits':588}.items()),counts
            else:
                assert all(counts[k]==v for k,v in {'permutations':362880,'simulations':2903040,'ticks':86728320,'halts':725760,'rays':2177280,'limits':0,'frames':0,'unsafe':0}.items()),counts
            results[name]=counts
    (args.output/'receipt.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
