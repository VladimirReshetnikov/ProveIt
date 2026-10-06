"""Optional-script output policy: stdout by default, exclusive external files."""
import argparse
import json
import os
from pathlib import Path
import stat


def need(condition, message):
    if not condition:
        raise ValueError(message)


def finish(value, reference):
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,help='new output JSON outside package')
    parser.add_argument('--compare',action='store_true',help='compare with bundled reference')
    args = parser.parse_args()
    if args.compare:
        expected = json.loads(reference.read_text())
        need(value == expected, 'result differs from bundled reference; inspect dependency versions and numeric precision')
    data = json.dumps(value,indent=2,allow_nan=False)+'\n'
    if args.output:
        target = args.output.absolute()
        need('..' not in target.parts,'unsafe output path')
        for parent in reversed(target.parents):
            need(stat.S_ISDIR(parent.lstat().st_mode),'nonregular or symlinked parent')
        need(not os.path.lexists(target),'output already exists')
        root = Path(__file__).absolute().parent.parent
        need(not target.resolve().is_relative_to(root.resolve()),'output must be outside package')
        with target.open('x',encoding='utf-8') as handle:
            handle.write(data)
    print(data,end='')
