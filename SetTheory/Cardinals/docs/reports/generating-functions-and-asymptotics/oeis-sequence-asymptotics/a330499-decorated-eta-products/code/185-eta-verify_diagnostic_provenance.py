#!/usr/bin/env python3
"""Validate optional source/receipt fingerprints using only the standard library.

This checks stored provenance and finite-receipt structure. It does not execute
numerical dependencies or independently certify stored floating-point values.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).absolute().parent))
import verify_manifest as manifest
ROOT=Path(__file__).absolute().parent
SOURCES=frozenset('optional/'+name+'.py' for name in ('_common','_mp','diagnostics','laguerre_check',
                    'check_two_point_decoration','fft_experiment','inverse_experiment','run_all'))
HISTORICAL=frozenset('optional/historical/'+name for name in ('explore.json','inverse_experiment.json',
                    'fft_experiment.json','replay.json','check_two_point_decoration.txt'))
ROUTES=frozenset(('precision_replay','laguerre_finite_jet','two_point_decoration','fft_eta_extraction','smooth_inverse'))

def verify(root=ROOT):
    root=manifest.check_directory(root)
    data=manifest.load_json(manifest.read_regular(root/'data/diagnostic_provenance.json'))
    manifest.need(isinstance(data,dict) and data.get('schema_version')==1 and
                  data.get('report')=='Report185' and data.get('sequence')=='A330499','wrong optional provenance identity')
    entries=data.get('adaptations')
    manifest.need(isinstance(entries,list) and len(entries)==len(SOURCES),'wrong optional source count')
    seen=set()
    for entry in entries:
        manifest.need(isinstance(entry,dict),'invalid optional adaptation')
        name=entry.get('path');manifest.safe_name(name)
        manifest.need(name in SOURCES and name not in seen,'unexpected or duplicate optional source')
        seen.add(name)
        path=root/name;manifest.check_directory(path.parent)
        manifest.need(hashlib.sha256(manifest.read_regular(path)).hexdigest()==entry.get('sha256'),
                      'optional source fingerprint differs: '+name)
    manifest.need(seen==SOURCES,'missing optional source')
    record=data.get('precomputed_receipt')
    manifest.need(isinstance(record,dict) and record.get('path')=='optional/receipts/all_optional.json','invalid optional receipt path')
    path=root/record['path'];manifest.check_directory(path.parent)
    content=manifest.read_regular(path)
    manifest.need(hashlib.sha256(content).hexdigest()==record.get('sha256'),'optional receipt fingerprint differs')
    receipt_digest=hashlib.sha256(content).hexdigest()
    receipt=manifest.load_json(content)
    manifest.need(isinstance(receipt,dict) and receipt.get('status')=='PASS' and receipt.get('schema_version')==1
                  and receipt.get('diagnostic')=='all_optional','invalid optional receipt identity')
    routes=receipt.get('receipts')
    manifest.need(isinstance(routes,dict) and set(routes)==ROUTES,'wrong optional receipt routes')
    for name,item in routes.items():
        manifest.need(isinstance(item,dict) and item.get('status')=='PASS' and item.get('diagnostic')==name
                      and isinstance(item.get('rows'),list) and bool(item['rows'])
                      and isinstance(item.get('checks'),dict) and bool(item['checks'])
                      and isinstance(item.get('boundary'),str) and 'not an interval certificate' in item['boundary'],
                      'invalid optional route receipt: '+name)
    historical=data.get('historical_numerical_outputs')
    manifest.need(isinstance(historical,list) and len(historical)==len(HISTORICAL),'wrong historical output count')
    historical_seen=set()
    original=data.get('original_numerical_evidence_sha256')
    manifest.need(isinstance(original,dict),'missing original numerical fingerprints')
    for item in historical:
        manifest.need(isinstance(item,dict) and set(item)=={'path','original_basename','bytes','sha256'},'invalid historical output record')
        name=item['path'];manifest.safe_name(name)
        manifest.need(name in HISTORICAL and name not in historical_seen,'unexpected or duplicate historical output')
        historical_seen.add(name)
        path=root/name;manifest.check_directory(path.parent);content=manifest.read_regular(path)
        manifest.need(type(item['bytes']) is int and item['bytes']==len(content),'historical output length differs')
        manifest.need(item['original_basename']==Path(name).name and
                      item['sha256']==original.get(item['original_basename'])==hashlib.sha256(content).hexdigest(),
                      'historical output fingerprint differs: '+name)
    manifest.need(historical_seen==HISTORICAL,'missing historical output')
    return {'status':'PASS','optional_source_fingerprints_checked':len(seen),
            'historical_numerical_output_fingerprints_checked':len(historical_seen),
            'precomputed_numerical_routes_checked':len(routes),
            'precomputed_receipt_sha256':receipt_digest,
            'numerical_dependencies_imported':False,'numerical_diagnostics_recomputed':False,
            'stored_values_certified':False}

if __name__=='__main__':
    try:print(json.dumps(verify(),sort_keys=True))
    except (ValueError,OSError,TypeError,KeyError) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr);sys.exit(1)
