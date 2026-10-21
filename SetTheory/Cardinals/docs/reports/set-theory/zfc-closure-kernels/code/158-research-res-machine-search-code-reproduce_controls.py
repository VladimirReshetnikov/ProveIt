#!/usr/bin/env python3
"""Replay C++ control synthesis and exhaustive independent Python comparison."""
from pathlib import Path
import argparse,json,shutil,subprocess
import verify_controls

ROOT=Path(__file__).resolve().parent.parent

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--cxx',default='g++');a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False)
    for name,source,table in [('equal','controls_two_row.cpp','two-row-control.tm'),
                              ('shifted','controls_shifted_two_row.cpp','shifted-control-1.tm')]:
        shutil.copyfile(ROOT/'controls'/table,a.output/table);exe=(a.output/('synthesize-'+name)).resolve()
        subprocess.run([a.cxx,'-std=c++20','-O3','-DNDEBUG',str(ROOT/'code'/source),'-o',str(exe)],check=True)
        with(a.output/f'controls-{name}-result.json').open('w')as out,(a.output/f'controls-{name}.log').open('w')as log:
            subprocess.run([str(exe),str(a.output/table),str(a.output/f'controls-{name}'),'30','3','1','2'],check=True,stdout=out,stderr=log)
    result=verify_controls.verify(a.output)
    (a.output/'exhaustive-agreement.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
