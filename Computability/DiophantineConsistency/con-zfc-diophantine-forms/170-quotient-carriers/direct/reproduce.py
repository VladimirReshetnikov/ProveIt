#!/usr/bin/env python3
"""Regenerate every new finite coefficient/map artifact in a temporary tree."""
from pathlib import Path
import argparse,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);args=ap.parse_args()
    folders=['diagonal_raw']+[f'diagonal{n}{suffix}' for n in [239,238] for suffix in ['', '_balanced','_centered','_reduced']]
    expected=[p.relative_to(ROOT) for name in folders for p in sorted((ROOT/name).glob('*.json'))]
    with tempfile.TemporaryDirectory(prefix='conzfc_diagonal_rebuild_') as td:
        temp=Path(td)
        shutil.copytree(ROOT/'baseline',temp/'baseline')
        for name in ['build.py','finish.py']:shutil.copy2(ROOT/name,temp/name)
        logs=[]
        for name in ['build.py','finish.py']:
            r=subprocess.run([sys.executable,'-B',str(temp/name)],check=True,capture_output=True,text=True)
            logs.append({'command':name,'stdout':r.stdout})
        for relative in expected:
            if (temp/relative).read_bytes()!=(ROOT/relative).read_bytes():
                raise ValueError('Reconstruction mismatch: '+str(relative))
    result={'status':'PASS','files_compared':len(expected),'all_bytes_identical':True,'commands':logs,
      'scope':'Deterministic regeneration of every new source, map, coefficient array and metric. Original baseline and emitted objects unchanged.'}
    out=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:args.receipt.write_text(out)
    print(out,end='')

if __name__=='__main__':main()
