"""Strict saved-packet replay allowing the delivered source_three_handles annotation."""
from contextlib import ExitStack
import hashlib
import json
from pathlib import Path
import sys
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.integer_codec import encoded_integer


def unique(pairs):
    d={}
    for k,v in pairs:
        if k in d: raise ValueError('duplicate key')
        d[k]=v
    return d


def reject(value): raise ValueError('noninteger JSON number')


records=[]
names=['normal_cut_handlebodies.normal_cut_handlebodies',
       'normal_cut_groups._group_terminal', 'normal_cut_groups._group_result',
       'normal_cut_groups.normal_cut_group_handlebodies',
       'normal_cut_groups.compile_disk_cut_presentation',
       'normal_cut_groups.certify_free_group',
       'source_cut_group.compile_disk_cut_presentation',
       'free_group_elimination.certify_free_group']
with ExitStack() as stack:
    for name in names: stack.enter_context(patch('fastunknot.'+name,side_effect=AssertionError(name)))
    for path in sorted((ROOT/'reports/111/certificates/group').glob('*.json')):
        raw=path.read_bytes(); p=json.loads(raw,object_pairs_hook=unique,parse_float=reject,parse_constant=reject)
        assert set(p)=={'source','certificate'}
        s=p['source']; required={'id','triangulation','coordinates'}
        assert set(s) in (required,required|{'source_three_handles'})
        for row in s['coordinates']:
            assert type(row) is list and len(row)==7
            for value in row: encoded_integer(value)
        c=p['certificate']
        if 'source_three_handles' in s:
            assert type(s['source_three_handles']) is int
            assert s['source_three_handles']==len(c['parallelity']['geometry']['core']['handles3'])
        assert verify_normal_cut_handlebodies(s['triangulation'],s['coordinates'],c),path.name
        records.append(dict(file=path.name,id=s['id'],sha256=hashlib.sha256(raw).hexdigest(),verified=True))
result=dict(passed=True,packets=len(records),records=records,disabled_producers=names,
            source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'fast/fastunknot').glob('*.py'))})
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(passed=True,packets=len(records))))
