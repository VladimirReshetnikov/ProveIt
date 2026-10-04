#!/usr/bin/env python3
"""Read-only standard-library replay of the recovered science packet."""
if not __debug__:raise RuntimeError('Optimized Python unsupported')
import argparse,hashlib,importlib.util,json,pathlib,sys
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parent

def need(test,why):
    if not test:raise RuntimeError(why)
def imported(name):
    spec=importlib.util.spec_from_file_location('own_'+name,ROOT/(name+'.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def verify(expected=None):
    raw=(ROOT/'MANIFEST.json').read_bytes();digest=hashlib.sha256(raw).hexdigest()
    if expected is not None:need(expected==digest,'External manifest pin mismatch')
    manifest=json.loads(raw)
    for rel,item in manifest['files'].items():
        p=ROOT/rel;need(p.is_file(),'Missing file: '+rel);b=p.read_bytes()
        need(len(b)==item['bytes']and hashlib.sha256(b).hexdigest()==item['sha256'],'Changed file: '+rel)
    mod=imported('merged_source');results=[]
    for a,name in[(2,'two-input-receipt.json'),(1,'one-input-receipt.json')]:
        actual=mod.build(arity=a);want=json.loads((ROOT/name).read_text());need(actual==want,'Replayed receipt mismatch')
        need(actual['recovery']['canonical_stream_byte_identity_verified'],'Old arithmetic identity not recovered')
        need(actual['fixed_coefficient_port_count']==1152598,'Coefficient ledger')
        results.append({k:actual[k]for k in['raw_port_count','single_polynomial','source_sha256','recovery']})
    degree=imported('check_exact_degree').calc();guards=imported('check_output_boundaries').check()
    return {'status':'PASS_FRESH_RECOVERED_PACKET_REPLAY','manifest_sha256':digest,'manifest_files':len(manifest['files']),'results':results,'degree':degree,'guards':guards,'no_upstream_code_recipe_or_schedule_execution':True}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--manifest-sha256');a=p.parse_args();print(json.dumps(verify(a.manifest_sha256),indent=2))
