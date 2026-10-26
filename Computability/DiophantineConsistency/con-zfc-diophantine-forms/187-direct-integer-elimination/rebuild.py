#!/usr/bin/env python3
"""Rebuild the joint source and every frozen monic circuit in another folder."""
from pathlib import Path
import argparse,contextlib,hashlib,io,json,shutil,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import build_joint,producer

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    out=a.output.resolve()
    if out==ROOT.resolve():p.error('Choose another output directory')
    (out/'source').mkdir(parents=True,exist_ok=True)
    shutil.copyfile(ROOT/'source/anchor219.json',out/'source/anchor219.json')
    old=build_joint.ROOT;build_joint.ROOT=out
    try:
        with contextlib.redirect_stdout(io.StringIO()):build_joint.build()
    finally:build_joint.ROOT=old
    if (ROOT/'joint209.json').read_bytes()!=(out/'joint209.json').read_bytes():
        raise ValueError('Joint source failed exact reproduction')
    (out/'equations').mkdir(exist_ok=True);reports=[]
    for source in sorted((ROOT/'equations').glob('integer*.json')):
        frozen=json.loads(source.read_text())
        generated=producer.build({'steps':frozen['elimination_steps']},out/'joint209.json')
        raw=(json.dumps(generated,sort_keys=True,separators=(',',':'))+'\n').encode()
        if raw!=source.read_bytes():raise ValueError('Circuit failed exact reproduction: '+source.name)
        (out/'equations'/source.name).write_bytes(raw)
        reports.append({'file':source.name,'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)})
    print(json.dumps({'status':'PASS','joint_source_rebuilt':True,'byte_identical_circuits':reports},sort_keys=True))
if __name__=='__main__':main()
