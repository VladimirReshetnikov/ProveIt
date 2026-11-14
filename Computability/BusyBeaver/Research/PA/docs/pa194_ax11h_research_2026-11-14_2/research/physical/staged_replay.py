#!/usr/bin/env python3
"""Replay neutral row rewrites followed by local pair-merger synthesis.

This is a finite-window candidate screen, not a source-equivalence proof.
It is optional and takes several minutes; replay.py checks the basic screens.
"""
from pathlib import Path
import argparse,json,subprocess,tempfile
from concurrent.futures import ThreadPoolExecutor
from replay import counters
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--jobs',type=int,default=1)
    args=ap.parse_args();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    table=ROOT/'inputs/QAX11H194.native.tm';windows=ROOT/'inputs/QAX11H194.contexts.txt'
    original={}
    for line in table.read_text().splitlines():
        q,b,w,d,n=line.split();original[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
    frozen=(ROOT/'results/neutral_candidates.jsonl').read_text()
    expected=json.loads((ROOT/'results/staged_results.json').read_text())
    results=[]
    with tempfile.TemporaryDirectory(dir=out,prefix='compile-') as temp:
        tmp=Path(temp)
        for program in ['neutral_rows','joint_return_merge']:
            subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'code'/f'{program}.cpp'),'-o',str(tmp/program)],check=True)
        p=subprocess.run([str(tmp/'neutral_rows'),str(table),'4','100',str(windows)],capture_output=True,text=True,check=True)
        assert p.stdout==frozen,'Neutral proposal list changed'
        candidates=[json.loads(line) for line in frozen.splitlines()]
        assert len(expected)==len(candidates)
        def run(item):
            i,edit=item;r=original.copy();assert tuple(edit['old'])==r[edit['state'],edit['read']]
            r[edit['state'],edit['read']]=tuple(edit['new']);candidate=tmp/f'candidate{i}.tm'
            candidate.write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n' for (q,b),(w,d,n) in sorted(r.items())))
            p=subprocess.run([str(tmp/'joint_return_merge'),str(candidate),'4','100',str(windows)],capture_output=True,text=True,check=True)
            got=counters(p.stderr);candidate.unlink()
            assert not p.stdout.strip(),(i,p.stdout)
            assert got==expected[i]['counters'],(i,got,expected[i])
            return {'index':i,'edit':edit,'counters':got}
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for rec in pool.map(run,enumerate(candidates)):
                results.append(rec);print('PASS',rec['index'],flush=True)
    (out/'staged_replay.json').write_text(json.dumps({'status':'PASS','results':results},indent=2)+'\n')
if __name__=='__main__':main()
