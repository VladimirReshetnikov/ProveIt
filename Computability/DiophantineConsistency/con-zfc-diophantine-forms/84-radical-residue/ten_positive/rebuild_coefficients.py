#!/usr/bin/env python3
"""Rebuild every fixed coefficient from the literal machine, in a temporary folder.

The unchanged source44 recipe is a pinned, credited upstream dependency.
The output payloads are compared by integer bytes, not gzip container headers.
"""
from pathlib import Path
import gzip, hashlib, importlib.util, json, shutil, tempfile

ROOT = Path(__file__).resolve().parent

def check(ok, msg):
    if not ok: raise ValueError(msg)

def run():
    binding = json.loads((ROOT/'coefficients/BINDING.json').read_text())
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for item in pins['files']:
        check(hashlib.sha256((ROOT/item['local']).read_bytes()).hexdigest() == item['sha256'],
              'Pinned source altered: '+item['local'])
    with tempfile.TemporaryDirectory() as folder:
        folder = Path(folder)
        for name in ['compact44_recipe.py','k215_transitions.json']:
            shutil.copyfile(ROOT/'upstream'/name,folder/name)
        spec=importlib.util.spec_from_file_location('source44_recipe',folder/'compact44_recipe.py')
        mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
        data=mod.recipe()
        finite=mod.finite_audit(data)
        controller=mod.padding_certificate(data)
        materialized=mod.materialize(data)
        reports=[]
        for name,entry in binding['ports'].items():
            raw=gzip.decompress((ROOT/'coefficients'/entry['gzip_payload']).read_bytes())
            built=gzip.decompress((folder/'coefficients'/entry['gzip_payload']).read_bytes())
            check(raw==built, 'Rebuilt coefficient differs: '+name)
            check(hashlib.sha256(raw).hexdigest()==entry['sha256'], 'Coefficient hash: '+name)
            reports.append({'port':name,'bits':int.from_bytes(raw,'little').bit_length(),
                            'raw_bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
    result={'status':'PASS','coefficients':reports,'total_raw_bytes':sum(x['raw_bytes'] for x in reports),
            'native_geometry_check':finite,'padding_controller_check':controller,
            'scope':'Exact finite tuple reconstruction and source identity; not an unbounded native semantic proof.'}
    (ROOT/'generated'/'COEFFICIENT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    r=run();print(json.dumps({'status':r['status'],'total_raw_bytes':r['total_raw_bytes']},indent=2))
