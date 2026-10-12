"""Preserve all earlier witnesses and check the source dual-forest extension."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[2]
DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.seeds import sources

def baseline(name):
    key='fastunknot._three_handle_baseline_'+name
    spec=importlib.util.spec_from_file_location(key,DATA/'three-handle-baseline'/(name+'.py'))
    module=importlib.util.module_from_spec(spec);sys.modules[key]=module;spec.loader.exec_module(module)
    return getattr(module,name if name=='normal_cut_handlebodies' else 'verify_normal_cut_handlebodies')


def main():
    pins=sources();old=baseline('normal_cut_handlebodies');verify=baseline('normal_cut_handlebodies_verify')
    bank=json.loads((ROOT/'fast/marked_parallelity_research/corpus.json').read_text())['cases']
    historical={r['id']:r for r in json.loads((DATA/'column-peeling-audit.json').read_text())['cases']}
    records=[]
    for c in bank:
        raw,rows=c['triangulation'],c['coordinates']
        a=old(raw,rows,record_certificate=True);b=normal_cut_handlebodies(raw,rows,record_certificate=True)
        row=dict(id=c['id'],before=a['status'],after=b['status'],reason=b.get('reason'))
        assert a['status']==historical[c['id']]['native_status']
        if a['status']=='COMPLETE':
            assert a['certificate']==b['certificate']
            assert verify(raw,rows,a['certificate']) and verify_normal_cut_handlebodies(raw,rows,a['certificate'])
            encoded=json.dumps(json_safe(a['certificate']),sort_keys=True).encode()
            assert hashlib.sha256(encoded).hexdigest()==historical[c['id']]['certificate_sha256']
        if b['status']=='COMPLETE':
            assert verify_normal_cut_handlebodies(raw,rows,b['certificate'])
            row.update(schema=b['certificate']['schema'],histogram=b['census']['histogram'])
        if a['status']!=b['status']:
            assert a['reason']=='core_has_three_handles' and b['status']=='COMPLETE'
            nofilter=normal_cut_handlebodies(raw,rows,record_certificate=True,precheck_core=False)
            assert nofilter['certificate']==b['certificate']
        records.append(row)
        if len(records)%10==0:print(len(records),flush=True)
    assert pins==sources()
    result=dict(native_source_sha256=pins,cases=records,unchanged_certificates=85,
                new_certificates=sum(r['before']!=r['after'] for r in records))
    assert result['new_certificates']==7
    Path(__file__).with_suffix('.json').write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print('All 85 older certificates unchanged; seven additional source certificates.')


if __name__=='__main__':main()
