#!/usr/bin/env python3
"""Corruption guards for release hashes, exact reference bytes, and output paths."""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest import mock
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent.parent
sys.path[:0]=[str(ROOT),str(ROOT/'code')]
import reproduce
import verify_manifest as manifest
import verify_frozen_sources as frozen
import verify_diagnostic_provenance as diagnostic

def run_tests():
    accepted=[];rejected=[]
    def good(label,condition):
        if not condition:raise ArithmeticError(label)
        accepted.append(label)
    def bad(label,operation):
        try:operation()
        except (ArithmeticError,ValueError,OSError,TypeError,KeyError):
            rejected.append(label);return
        raise ArithmeticError('guard failed: '+label)
    good('valid frozen sources',frozen.verify(ROOT)['status']=='PASS')
    with tempfile.TemporaryDirectory(prefix='report185-replay-guards-') as temporary:
        base=Path(temporary);copy=base/'source';copy.mkdir()
        for name in list(frozen.EXPECTED)+['data/FROZEN_SOURCE_HASHES.json']:
            path=copy/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes((ROOT/name).read_bytes())
        good('valid copied sources',frozen.verify(copy)['status']=='PASS')
        for name in list(diagnostic.SOURCES)+list(diagnostic.HISTORICAL)+['data/diagnostic_provenance.json','optional/receipts/all_optional.json']:
            path=copy/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes((ROOT/name).read_bytes())
        good('valid optional provenance',diagnostic.verify(copy)['status']=='PASS')
        optional_source=copy/'optional/diagnostics.py';original_optional=optional_source.read_bytes()
        optional_source.write_bytes(original_optional+b'\n')
        bad('changed optional source',lambda:diagnostic.verify(copy))
        optional_source.write_bytes(original_optional)
        optional_receipt=copy/'optional/receipts/all_optional.json';original_optional_receipt=optional_receipt.read_bytes()
        optional_receipt.write_bytes(original_optional_receipt.replace(b'PASS',b'FAIL',1))
        bad('changed optional receipt',lambda:diagnostic.verify(copy))
        optional_receipt.write_bytes(original_optional_receipt)
        optional_provenance=copy/'data/diagnostic_provenance.json';original_provenance=optional_provenance.read_bytes()
        data=manifest.load_json(original_provenance);data['adaptations'][-1]=data['adaptations'][0]
        optional_provenance.write_text(json.dumps(data))
        bad('duplicate optional provenance path',lambda:diagnostic.verify(copy))
        optional_provenance.write_bytes(original_provenance)
        historical=copy/'optional/historical/fft_experiment.json';historical_bytes=historical.read_bytes()
        historical.write_bytes(historical_bytes+b'\n')
        bad('changed historical numerical output',lambda:diagnostic.verify(copy))
        historical.write_bytes(historical_bytes)
        source=copy/'code/verify_exact.py';source.write_bytes(source.read_bytes()+b'\n')
        bad('changed exact source',lambda:frozen.verify(copy))
        source.write_bytes((ROOT/'code/verify_exact.py').read_bytes())
        original_source=source.read_bytes()
        source.write_bytes(bytes([original_source[0]^1])+original_source[1:])
        bad('same-length changed exact source',lambda:frozen.verify(copy))
        source.write_bytes(original_source)
        exact_receipt=copy/'certificates/exact_checks.json'
        original_exact=exact_receipt.read_bytes()
        exact_receipt.write_bytes(original_exact.replace(b'PASS',b'FAIL',1))
        bad('changed exact reference receipt',lambda:frozen.verify(copy))
        exact_receipt.write_bytes(original_exact)
        receipt=copy/'data/FROZEN_SOURCE_HASHES.json'
        original=receipt.read_bytes();data=manifest.load_json(original);data['files'].pop('data/fixture21.json')
        receipt.write_text(json.dumps(data));bad('missing frozen inventory',lambda:frozen.verify(copy))
        receipt.write_bytes(original);data=manifest.load_json(original);data['files']['data/fixture21.json']['bytes']=True
        receipt.write_text(json.dumps(data));bad('boolean byte length',lambda:frozen.verify(copy))
        receipt.write_bytes(original);data=manifest.load_json(original);data['report']=186
        receipt.write_text(json.dumps(data));bad('wrong report identity',lambda:frozen.verify(copy))
        receipt.write_bytes(original)
        bad('output source root',lambda:reproduce.validate_output(copy,copy))
        bad('output source child',lambda:reproduce.validate_output(copy,copy/'child'))
        existing=base/'existing';existing.mkdir();(existing/'sentinel').write_bytes(b'keep')
        bad('output existing directory',lambda:reproduce.validate_output(copy,existing))
        good('existing output preserved',(existing/'sentinel').read_bytes()==b'keep')
        link=base/'link';link.symlink_to(base/'absent')
        bad('output dangling symlink',lambda:reproduce.validate_output(copy,link))
        bad('output traversal',lambda:reproduce.validate_output(copy,base/'existing'/'..'/'new'))
        with mock.patch.object(subprocess,'run',return_value=subprocess.CompletedProcess(['fixture'],1,'','failed')):
            bad('failed subprocess',lambda:reproduce.run_script(copy,'fixture.py',base))
        for text in ('{}','[]','{"status":"FAIL"}','{"status":"FAIL","status":"PASS"}','{"status":"PASS","value":NaN}'):
            with mock.patch.object(subprocess,'run',return_value=subprocess.CompletedProcess(['fixture'],0,text,'')):
                bad('invalid subprocess result '+text,lambda:reproduce.run_script(copy,'fixture.py',base))
        with mock.patch.object(subprocess,'run',return_value=subprocess.CompletedProcess(['fixture'],0,'{"status":"PASS"}','')) as runner:
            good('valid subprocess result',reproduce.run_script(copy,'fixture.py',base,True)=={'status':'PASS'})
            command=runner.call_args.args[0]
            good('isolated optimized stdlib invocation',command[1:5]==['-I','-S','-B','-O'])
            good('subprocess shell disabled',runner.call_args.kwargs['shell'] is False)
    return {'status':'PASS','positive_tests':len(accepted),'negative_tests':len(rejected),'assertions_required':False}

if __name__=='__main__':
    try:print(json.dumps(run_tests(),sort_keys=True))
    except (ArithmeticError,ValueError,OSError,TypeError) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr);sys.exit(1)
