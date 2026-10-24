#!/usr/bin/env python3
"""Rebuild both supplied equations into a temporary directory and compare bytes."""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse,json
import build_modular_factorial as builder
from verify import run

HERE=Path(__file__).resolve().parent


def reproduce():
    records=[]
    with TemporaryDirectory(prefix='con-zfc-merged-factorial-') as td:
        for name,syntax in [('equation319','cantor'),('equation320','xx0')]:
            output=Path(td)/name
            builder.generate(output,syntax,'power',True,True)
            original=HERE/name
            files=sorted(p.relative_to(original) for p in original.rglob('*.json'))
            generated=sorted(p.relative_to(output) for p in output.rglob('*.json'))
            if files!=generated:raise ValueError('generated file inventory differs')
            for relative in files:
                if (original/relative).read_bytes()!=(output/relative).read_bytes():
                    raise ValueError('rebuilt bytes differ: '+str(relative))
            checked=run(output)
            records.append({'equation':name,'byte_identical_files':len(files),
                            'metrics':checked['metrics']})
    return {'status':'PASS','equations':records,'network_used':False,
            'dependencies':'Python 3 standard library only'}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
    text=json.dumps(reproduce(),indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')
