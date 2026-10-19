#!/usr/bin/env python3
"""Compile and replay the finite arbitrary-row fusion family for one layout."""
from pathlib import Path
import argparse,json,subprocess,time
import make_cases

HERE=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--layout',choices=make_cases.LAYOUTS,default='baseline')
    parser.add_argument('--scope',choices=('all','admissible','product'),default='product')
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--cxx',default='c++')
    args=parser.parse_args()
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=True)
    content,generated=make_cases.generate(args.layout,args.scope,None)
    source=HERE/'arbitrary_row_search.cpp';binary=output/'arbitrary_row_search'
    subprocess.run([args.cxx,'-O3','-std=c++17',str(source),'-o',str(binary)],check=True)
    began=time.monotonic()
    with (output/'search.log').open('w') as log:
        subprocess.run([str(binary),'-'],input=content,text=True,cwd=output,stdout=log,stderr=subprocess.STDOUT,check=True)
    result=dict(generated_inputs=generated,elapsed_seconds=time.monotonic()-began,
        source_sha256=make_cases.sha(source),fixture_streamed_on_stdin=True,
        result=json.loads((output/'arbitrary-row-summary.json').read_text()))
    (output/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
