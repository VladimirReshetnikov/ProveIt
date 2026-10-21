#!/usr/bin/env python3
"""Rebuild the frozen exact source certificate, using Python's standard library."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile
import build_dominated_source as b
ROOT=Path(__file__).resolve().parent

def main():
    manifest=json.loads((ROOT/'manifest.json').read_text())
    for name,expected in manifest['files'].items():
        actual=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
        assert actual==expected,('file identity mismatch',name,actual,expected)
    with tempfile.TemporaryDirectory(prefix='proveit_source218_')as tmp:
        result=subprocess.run([sys.executable,str(ROOT/'build_dominated_source.py'),str(ROOT/'baseline_sites219.json'),tmp,'--common','--equivalent',str(ROOT/'sites218.json')],check=True,capture_output=True,text=True)
        expected=json.loads((ROOT/'source_receipt.json').read_text())
        actual=json.loads((Path(tmp)/'source_receipt.json').read_text())
        assert actual==expected,'Rebuilt receipt differs from frozen source receipt'
        assert (Path(tmp)/'dominated_zyx206.json').read_bytes()==(ROOT/'dominated_zyx206.json').read_bytes()
    rows=json.loads((ROOT/'sites218.json').read_text())
    graph=b.cfg_intervals(rows)
    assert graph==b.cfg_arithmetic(rows)
    assert b.compact(graph)==(ROOT/'ordinal_cfg.json').read_bytes()
    primitives=sorted(set((o,r)for _,o,r in rows))
    assert len(primitives)==23
    assert {r for o,r in primitives if o=='CC'}=={1,2,3}
    print(json.dumps(dict(status='VERIFIED_EXACT_SOURCE_CALIBRATION_CERTIFICATE',source_sha256=expected['equivalent_source']['sha256'],metrics=expected['equivalent_source']['metrics'],guarded_cases=expected['equivalent_source']['guarded_cases'],primitive_kinds=23,cc_arguments=[1,2,3],preserved_outer_paths=186,scope='All-register source bisimulation and literal outer-address preservation; binary runtime and startup certified separately.'),indent=2))
if __name__=='__main__':main()
