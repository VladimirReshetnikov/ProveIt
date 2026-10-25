#!/usr/bin/env python3
"""Two fixed common-name charts. CODE ONLY/HOLD until separate root release."""
import argparse, hashlib, importlib.util, json, sys, tempfile
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RAW = ROOT/'research/round16-square-weighted-projections'
PLAN = ROOT/'research/round16-common-name-centering-plan'
OLD = ROOT/'research/signed-pell-cap-nine-factor-projections'
SEALS = {'research/round16-square-weighted-projections':'34b2b1b6f27dea48cfc7692ad64e5a034304e76cb0d3ef47eae87ec194862acd',
         'research/round16-common-name-centering-plan':'ed0f0365d85209797f50fd450bde8b929fc853772e9ae2fb1d1346d090bff4e1',
         'research/signed-pell-cap-nine-factor-projections':'c48ecc2d0cf12e125ecc9ab45849073e6d06a303a38e130aa6fd42859168aefd'}
PROFILES = ['plain','weighted']
POLICY = dict(name='fixed58_common_names', profiles=PROFILES, shifts_per_profile=58,
              search=False, optional_initial_recipe=False, raw_coordinates_preserved=True)

def need(ok, why):
    if not ok: raise ValueError(why)
def get(p): return json.loads(p.read_bytes())
def canon(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(b): return hashlib.sha256(b).hexdigest()
def sha(x): return digest(canon(x))
def meta(p):
    b=p.read_bytes(); return dict(bytes=len(b),sha256=digest(b))
def inventory(p, skip='INDEX.json'):
    return {str(q.relative_to(p)):meta(q) for q in sorted(p.rglob('*'))
            if q.is_file() and q != p/skip}
def put(p,x):
    p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(canon(x))

def authenticate():
    pins=get(HERE/'SOURCE_PINS.json'); need(pins['closed_dependencies']==SEALS,'exact three sealed parents')
    for n,m in pins['files'].items(): need(meta(ROOT/n)==m,'external '+n)
    for n,m in pins['core'].items(): need(meta(HERE/n)==m,'reviewed core '+n)
    for n,m in pins['vendor'].items(): need(meta(HERE/'vendor'/n)==m,'reviewed vendor '+n)
    for n,s in SEALS.items():
        p=ROOT/n; need(meta(p/'MANIFEST.json')['sha256']==s,'parent seal '+n)
        d=get(p/'MANIFEST.json')['files']; a=inventory(p,'MANIFEST.json')
        need(d=={k:v if isinstance(d.get(k),dict) else v['sha256'] for k,v in a.items()},'whole parent inventory '+n)
    held=get(HERE/'HOLD_INVENTORY.json')['files']
    need(all(meta(HERE/n)==m for n,m in held.items()),'all original held bytes')
    if (HERE/'MANIFEST.json').exists():
        need(get(HERE/'MANIFEST.json')['files']==inventory(HERE,'MANIFEST.json'),'whole final author inventory')
    return meta(HERE/'SOURCE_PINS.json')['sha256']

def safe(path, receipt=False):
    path=path.absolute(); need(not any(q.is_symlink() for q in [path,*path.parents]),'no symlink output path')
    target=path.resolve(); pins=get(HERE/'SOURCE_PINS.json')
    need(not any(target.is_relative_to((ROOT/n).resolve()) for n in SEALS),'never write sealed parents')
    need(target not in {(ROOT/n).resolve() for n in pins['files']},'never overwrite pinned external input')
    need(not target.is_relative_to(HERE/'vendor'),'never write reviewed vendor')
    need(target not in {HERE/n for n in list(pins['core'])+['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json']},'never write reviewed core')
    if receipt:
        need(not target.is_relative_to(HERE/'data'),'receipt outside data')
        need(not (HERE/'MANIFEST.json').exists() or not target.is_relative_to(HERE),'receipt outside sealed packet')
    else: need(not HERE.is_relative_to(target),'destination cannot contain author code')

def fixed_policy():
    p=get(PLAN/'SOURCE_PINS.json')['policy']
    need(p['perform_search'] is False and p['all_other_shifts']==0 and len(p['shifts'])==58,'fixed plan policy')
    return dict(name=POLICY['name'],plan_manifest_sha256=SEALS[str(PLAN.relative_to(ROOT))],
        old_recipe_manifest_sha256=SEALS[str(OLD.relative_to(ROOT))],
        old_recipe_certificate=meta(OLD/'data/centered/translation_certificate.json'),
        name_index_association=p['shifts'],absent_old_nonzero_shifts=p['absent_old_nonzero_shifts'],
        all_other_shifts=0,search=False)

def census(eq,poly):
    used=sorted({i for r in eq['residuals'] for c,m in r['terms'] if c for i in m})
    return dict(variables=len(eq['variables']),rows=len(eq['residuals']),degree=max((len(m) for c,m in poly['terms']),default=0),
        monomials=len(poly['terms']),height=max((abs(c) for c,m in poly['terms']),default=0),
        row_height=max((abs(c) for r in eq['residuals'] for c,m in r['terms']),default=0),
        used_coordinates=used,unconstrained_coordinates=sorted(set(range(len(eq['variables'])))-set(used)))

def composed(name,raw,chart,cert):
    parent=get(RAW/'data'/name/'COMPOSED_MAPS.json')
    return dict(schema='round16_translated_composed_integer_maps_v1',profile=name,
        raw_parent_manifest_sha256=SEALS[str(RAW.relative_to(ROOT))],raw_projected_sha256=sha(raw),chart_sha256=sha(chart),
        translation=dict(shifts=cert['shifts'],raw_to_chart='z_i = x_i - delta_i',chart_to_raw='x_i = z_i + delta_i'),
        all_raw_coordinates_retained=True,parent_maps=parent,
        source_binding=get(RAW/'data'/name/'SOURCE_BINDING.json'),
        raw_endpoint_binding=get(RAW/'data'/name/'ENDPOINT_BINDING.json'),
        inverse_order=['add_fixed_delta_to_recover_raw_projected_tuple']+parent['inverse_order'],
        forward_order=parent['forward_order']+['subtract_fixed_delta_from_raw_projected_tuple'],
        no_old_private_tuple_identity=True,original_native_or_source_program_rerun=False)

def materialize(destination,pinhash):
    safe(destination); need(not destination.exists() or not any(destination.iterdir()),'destination must be empty')
    destination.mkdir(parents=True,exist_ok=True)
    # Exact authenticated modules only; no optimizer or source entry point is called.
    spec=importlib.util.spec_from_file_location('terminal_elimination',HERE/'vendor/terminal_elimination.py')
    E=importlib.util.module_from_spec(spec); sys.modules['terminal_elimination']=E; spec.loader.exec_module(E)
    spec=importlib.util.spec_from_file_location('fixed_translate',HERE/'vendor/translate_coordinates.py')
    T=importlib.util.module_from_spec(spec); spec.loader.exec_module(T)
    need(T.E is E,'translator uses exact authenticated polynomial module')
    policy=fixed_policy(); summaries={}
    for name in PROFILES:
        raw=get(RAW/'data'/name/'projected.json'); byname={v['name']:i for i,v in enumerate(raw['variables'])}
        need(len(byname)==len(raw['variables']),'unique raw names')
        pairs=sorted([[q[name+'_index'],q['shift']] for q in policy['name_index_association']])
        need(len(pairs)==58 and len({i for i,s in pairs})==58,'exact58 distinct shifts')
        for q in policy['name_index_association']:
            need(byname[q['literal_name']]==q[name+'_index'] and type(q['shift']) is int and q['shift']!=0,'exact name/index/integer shift')
        chart=T.translate(raw,dict(pairs)); poly=E.expand(chart)
        cert=dict(schema='integral_translation_v1',profile=name,input_sha256=sha(raw),output_sha256=sha(chart),
            convention='old_coordinate = new_coordinate + shift',inverse='new_coordinate = old_coordinate - shift',
            shifts=pairs,fixed_policy=policy)
        values={'equation.json':chart,'expanded_polynomial.json':poly,'translation_certificate.json':cert,
                'METRICS.json':census(chart,poly),'COMPOSED_MAPS.json':composed(name,raw,chart,cert)}
        folder=destination/name
        for n,x in values.items(): put(folder/n,x)
        endpoint=dict(schema='round16_fixed_translation_endpoint_v1',profile=name,source_pins_sha256=pinhash,
            raw_parent_manifest_sha256=SEALS[str(RAW.relative_to(ROOT))],
            raw_data_index=meta(RAW/'data/INDEX.json'),all_prior_profile_files=inventory(folder),
            equivalence_chain=['fixed_integer_translation_bijection','complete_accepted_raw_projection_and_Horn_maps','whole_sealed_source_ordinary_calibration'],
            inverse_translation_before_raw_witness_maps=True,old327_polynomial_identity_claimed=False,search_or_optimality_claimed=False)
        put(folder/'ENDPOINT_BINDING.json',endpoint); summaries[name]=values['METRICS.json']
    index=dict(schema='round16_fixed_two_chart_inventory_v1',source_pins_sha256=pinhash,
        producer_sha256=meta(HERE/'build.py')['sha256'],policy=POLICY,summary=summaries,files=inventory(destination))
    put(destination/'INDEX.json',index); return index

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--check',action='store_true')
    p.add_argument('--destination',type=Path,default=HERE/'data'); p.add_argument('--output',type=Path,required=True)
    a=p.parse_args(); pinhash=authenticate(); safe(a.destination); safe(a.output,True)
    need(not a.output.resolve().is_relative_to(a.destination.resolve()),'receipt outside selected data')
    need(not (HERE/'MANIFEST.json').exists() or a.check,'sealed data immutable')
    if a.check:
        with tempfile.TemporaryDirectory(prefix='round16-fixed-centering-') as td:
            scratch=Path(td)/'data'; index=materialize(scratch,pinhash)
            actual={str(q.relative_to(a.destination)):q.read_bytes() for q in a.destination.rglob('*') if q.is_file()}
            expected={str(q.relative_to(scratch)):q.read_bytes() for q in scratch.rglob('*') if q.is_file()}
            need(actual==expected,'every deterministic rebuilt file byte')
    else: index=materialize(a.destination,pinhash)
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),pure_check=a.check,
        source_pins_sha256=pinhash,index_sha256=sha(index),data_files=len(index['files'])+1,summary=index['summary'],
        scope='Exactly two fixed58 charts; no search, new projection, global optimum or old-polynomial identity.')
    out=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
    need(not a.output.exists() or a.output.read_bytes()==out,'refuse changed receipt overwrite')
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_bytes(out); print(out.decode(),end='')
if __name__=='__main__': main()
