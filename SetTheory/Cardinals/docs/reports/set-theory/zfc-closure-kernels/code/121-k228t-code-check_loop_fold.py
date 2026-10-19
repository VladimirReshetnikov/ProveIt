#!/usr/bin/env python3
"""Recheck the optional all-tape 79-to-63 fold on the rotated K230 basis.

The reused local checker reserves halt label254. Only that halt label is
alpha-renamed for this computation; working labels are the released K230 labels.
The primary K228 correctness proof uses direct complete source runtime instead.
"""
from pathlib import Path
import argparse, hashlib, json
import verify_state_fold as fold


def normalized(raw):
    lines=[]
    for line in raw.decode().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,z=line.split()
            line=' '.join((q,b,w,d,'254' if z=='230' else z))
        lines.append(line)
    return ('\n'.join(lines)+'\n').encode()


def main():
    package=Path(__file__).resolve().parent.parent
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=package/'rerun/loop_fold_local.json')
    args=ap.parse_args()
    old_path,new_path=package/'machines/k230_rotated.tm',package/'machines/k229_loop.tm'
    old,os=fold.parse_table(normalized(old_path.read_bytes()))
    new,ns=fold.parse_table(normalized(new_path.read_bytes()))
    result=fold.prove(old,new,os,ns,63,79,0,None,5,65,20000)
    if result['status']!='PASS_ALL_TAPE_POSITIVE_BLOCK_SIMULATION':
        raise ValueError(result)
    if result['proved_old_rows']!=460 or result['block_length_histogram']!={1:456,3:3,9:1}:
        raise ValueError('Unexpected block census')
    result.update(old_sha256=hashlib.sha256(old_path.read_bytes()).hexdigest(),
                  new_sha256=hashlib.sha256(new_path.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(fold.__file__).read_bytes()).hexdigest(),
                  wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  halt_renaming={'230':254})
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: all460 old rows;456 one-step,3 three-step,1 nine-step blocks')


if __name__=='__main__':main()
