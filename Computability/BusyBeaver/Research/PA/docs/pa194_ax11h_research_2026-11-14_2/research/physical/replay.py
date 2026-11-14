#!/usr/bin/env python3
"""Replay the six frozen-window local reduction screens; no calibration claim."""
from pathlib import Path
import argparse,hashlib,json,subprocess,tempfile
ROOT=Path(__file__).resolve().parent

def counters(text):
    line=next(x for x in reversed(text.splitlines()) if x.startswith('DONE '))
    p=line.split()[1:]
    return {p[i]:int(p[i+1]) for i in range(0,len(p)-1,2) if p[i]!='seconds'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    expected=json.loads((ROOT/'results/summary.json').read_text())
    for name,h in json.loads((ROOT/'results/input_hashes.json').read_text()).items():
        assert hashlib.sha256((ROOT/'inputs'/name).read_bytes()).hexdigest()==h,name
    results=[]
    with tempfile.TemporaryDirectory(dir=out,prefix='compile-') as temp:
        tmp=Path(temp)
        for program in ['joint_return_merge','displaced_merge_all_starts']:
            subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'code'/f'{program}.cpp'),'-o',str(tmp/program)],check=True)
        for rec in expected['tables']:
            name=rec['name'];table=ROOT/'inputs'/f'{name}.native.tm';ctx=ROOT/'inputs'/f'{name}.contexts.txt'
            for kind,program in [('ordinary_merge','joint_return_merge'),('displaced_merge','displaced_merge_all_starts')]:
                args=([str(tmp/program),str(table),'4','100',str(ctx)] if kind=='ordinary_merge' else
                      [str(tmp/program),str(table),str(ctx),'4','100'])
                p=subprocess.run(args,capture_output=True,text=True,check=True)
                got=counters(p.stderr)
                assert not p.stdout.strip(),(name,kind,p.stdout)
                assert got==rec[kind],(name,kind,got,rec[kind])
                (out/f'{name}.{kind}.log').write_text(p.stderr)
                results.append({'name':name,'kind':kind,**got})
                print(name,kind,got,flush=True)
    (out/'replay.json').write_text(json.dumps({'status':'PASS','checks':results},indent=2)+'\n')
if __name__=='__main__':main()
