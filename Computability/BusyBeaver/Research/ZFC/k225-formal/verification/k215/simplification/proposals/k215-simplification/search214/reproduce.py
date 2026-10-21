#!/usr/bin/env python3
"""Verify the inputs/controls; optionally replay all six bounded searches."""
from pathlib import Path
import argparse,json,sys,tempfile,contextlib,io,hashlib

if not __debug__:
    raise SystemExit('Run without -O: this audit relies on Python assertions.')

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'tools'))
from check_controls import main as controls
from indexed_fold_search import search

def main():
    p=argparse.ArgumentParser();p.add_argument('--search',action='store_true');a=p.parse_args()
    result=controls()
    assert result['status']=='PASS'
    replay=[]
    for pin in json.loads((ROOT/'input_pins.json').read_text()):
        name=Path(pin['file']).stem
        expected=json.loads((ROOT/'evidence'/f'{name}.json').read_text())
        assert expected['machine_sha256']==pin['sha256']
        assert expected['all_pairs']==23005 and expected['survivors']==[]
        assert expected['overlap_screen'] is False
        assert expected['radius']==4 and expected['step_bound']==48
        assert expected['implementation_sha256']=={tool:hashlib.sha256((ROOT/'tools'/tool).read_bytes()).hexdigest()for tool in['indexed_fold_search.py','window_fold_search.py']}
        if a.search:
            with tempfile.TemporaryDirectory()as tmp:
                out=Path(tmp)/'result.json'
                with contextlib.redirect_stdout(io.StringIO()):search(ROOT/pin['file'],4,48,out)
                actual=json.loads(out.read_text())
            for key in set(expected)-{'seconds'}:assert actual[key]==expected[key],(name,key)
            replay.append(name)
    print(json.dumps({'status':'PASS','exact_inputs':6,'positive_control':True,'negative_controls':2,'stored_searches_audited':6,'searches_freshly_replayed':replay,'constructed214':False},indent=2))

if __name__=='__main__':main()
