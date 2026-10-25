#!/usr/bin/env python3
"""Two raw Round16 projection profiles. CODE ONLY/HOLD until explicit release."""
import argparse, hashlib, json, shutil, sys, tempfile
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / 'research/round16-square-weighted-source'
SOURCE_SEAL = 'b40d630005f7e8d682c513cb414b2063a47530dc2051a5b2757833f2e90a1be8'
PROFILES = ['plain', 'weighted']
POLICY = dict(max_support=16, affine_support=None, quadratic_first=False,
              profiles=PROFILES, charts='raw untranslated', pruning=False)

def need(ok, why):
    if not ok: raise ValueError(why)

def get(p): return json.loads(p.read_bytes())
def canon(x): return (json.dumps(x, sort_keys=True, separators=(',', ':'))+'\n').encode()
def digest(b): return hashlib.sha256(b).hexdigest()
def sha(x): return digest(canon(x))
def meta(p):
    b=p.read_bytes(); return dict(bytes=len(b), sha256=digest(b))
def inventory(p):
    return {str(q.relative_to(p)):meta(q) for q in sorted(p.rglob('*'))
            if q.is_file() and q != p/'INDEX.json'}
def put(p, x):
    p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(canon(x))

def authenticate():
    pins=get(HERE/'SOURCE_PINS.json')
    for n,m in pins['files'].items(): need(meta(ROOT/n)==m, 'whole input '+n)
    for n,m in pins['vendor'].items(): need(meta(HERE/'vendor'/n)==m, 'vendor '+n)
    for n,m in pins['core'].items(): need(meta(HERE/n)==m, 'author core '+n)
    for n,h in pins['closed_dependencies'].items():
        folder=ROOT/n; need(meta(folder/'MANIFEST.json')['sha256']==h, 'closed parent '+n)
        declared=get(folder/'MANIFEST.json')['files']
        actual={str(q.relative_to(folder)):meta(q) for q in folder.rglob('*')
                if q.is_file() and q != folder/'MANIFEST.json'}
        expected={n:m if isinstance(declared.get(n),dict) else m['sha256'] for n,m in actual.items()}
        need(declared==expected, 'every selected closed parent file '+n)
    need(meta(SOURCE/'MANIFEST.json')['sha256']==SOURCE_SEAL, 'whole accepted source seal')
    if (HERE/'MANIFEST.json').exists():
        actual={str(q.relative_to(HERE)):meta(q) for q in HERE.rglob('*')
                if q.is_file() and q != HERE/'MANIFEST.json'}
        need(get(HERE/'MANIFEST.json')['files']==actual, 'closed author inventory')
    return meta(HERE/'SOURCE_PINS.json')['sha256']

def safe(path, receipt=False):
    path=path.absolute()
    need(not any(q.is_symlink() for q in [path,*path.parents]), 'no symlink output path')
    target=path.resolve(); pins=get(HERE/'SOURCE_PINS.json')
    need(not any(target.is_relative_to((ROOT/n).resolve()) for n in pins['closed_dependencies']), 'never write frozen parents')
    need(target not in {(ROOT/n).resolve() for n in pins['files']}, 'never overwrite a pinned external file')
    need(not target.is_relative_to(HERE/'vendor'), 'never write vendor')
    need(target not in {HERE/n for n in list(pins['core'])+['SOURCE_PINS.json','HOLD_INVENTORY.json','MANIFEST.json']}, 'never replace reviewed inputs')
    if receipt:
        need(not target.is_relative_to(HERE/'data'), 'receipt outside generated data')
        need(not (HERE/'MANIFEST.json').exists() or not target.is_relative_to(HERE), 'receipt outside sealed packet')
    else:
        need(not HERE.is_relative_to(target), 'destination must not contain author code')

def horn_maps(E, src, dst, c):
    old=[E.normalize(r['terms']) for r in src['residuals']]
    new=[E.normalize(r['terms']) for r in dst['residuals']]
    sq=c['square_variables']; g=c['guard_variables']
    defs={s:next(i for i,r in enumerate(src['residuals'])
                  if r['label']=='nonnegative_square_difference' and old[i].get((s,))==1) for s in sq}
    h,u,z,d=(g[k] for k in ['h','old_second_square','g','old_D_square'])
    pr=next(i for i,p in enumerate(old) if E.candidate(p,z,False)==E.multiply({(h,):1},{(u,):1}))
    dr=next(i for i,p in enumerate(old) if E.candidate(p,d,False) is not None)
    targets={s:defs[s] for s in sq[:9]+sq[13:15]+[h,u,sq[11]]}
    targets.update({z:pr,d:dr}); targets.update({v:r for r,v in c['product_chain']})
    deleted=set(c['deleted_rows'])
    rm={i:j for j,i in enumerate(i for i in range(len(old)+1) if i not in deleted)}
    forward={v:rm[r] for v,r in targets.items() if v not in {u,d}}
    forward[c['new_root']]=len(new)-1
    def ordered(ds, rows):
        todo={v:(r,E.candidate(rows[r],v,False)) for v,r in ds.items()}; out=[]
        need(all(f is not None for r,f in todo.values()), 'monic Horn witness definitions')
        while todo:
            ready=[v for v,(r,f) in todo.items() if not {i for m in f for i in m}&set(todo)]
            need(ready, 'acyclic Horn witness rebuild'); v=min(ready); r,f=todo.pop(v)
            out.append(dict(coordinate=v,row=r,restoration=E.as_terms(f)))
        return out
    return dict(schema='round16_horn_existential_maps_v1', source_sha256=sha(src), factored_sha256=sha(dst),
        preserved_source_coordinates=sorted(set(range(len(src['variables'])))-set(targets)),
        overwritten_source_coordinates=sorted(targets),
        source_to_factored=dict(copy_source_coordinates=list(range(len(src['variables']))),
            initialize_factored_private_to_zero=sorted({u,d}),restorations=ordered(forward,new)),
        factored_to_source=dict(discard_factored_coordinates=[c['new_root']],
            copy_source_coordinates=list(range(len(src['variables']))),restorations=ordered(targets,old)),
        full_old_private_witness_identity_claimed=False,
        inverse_scope='Initialize every actual projection-free factored coordinate, reverse all monic steps, then overwrite obsolete original Horn-private witnesses.')

def census(eq, poly):
    used=sorted({i for r in eq['residuals'] for c,m in r['terms'] if c for i in m})
    return dict(variables=len(eq['variables']),rows=len(eq['residuals']),degree=max((len(m) for c,m in poly['terms']),default=0),
        monomials=len(poly['terms']),height=max((abs(c) for c,m in poly['terms']),default=0),
        row_height=max((abs(c) for r in eq['residuals'] for c,m in r['terms']),default=0),
        used_coordinates=used,unconstrained_coordinates=sorted(set(range(len(eq['variables'])))-set(used)))

def source_binding(name):
    return dict(schema='round16_projection_source_binding_v1',profile=name,source_manifest_sha256=SOURCE_SEAL,
        whole_source_file=meta(SOURCE/'data'/f'{name}.json'),
        source_context=meta(SOURCE/'data/SOURCE_CONTEXT.json'),whole_source_maps=meta(SOURCE/'data/ROW_MAPS.json'),
        ordinary_witness_maps=meta(SOURCE/'data/WITNESS_MAPS.json'),
        retained_calibration=get(SOURCE/'data/CALIBRATION_BINDING.json'),
        original_compiler_or_native_program_rerun=False,old324_polynomial_or_old327_body_identity=False,
        interval_triples_fresh_across_reparameterization=True,Hstar_H0_raw_tuple_identity=False)

def composed(src, factored, c, wm):
    return dict(schema='round16_composed_integer_maps_v1',source_coordinates=len(src['variables']),
        factored_coordinates=len(factored['variables']),source_to_factored=wm['source_to_factored'],
        factored_to_source=wm['factored_to_source'],preserved_source_coordinates=wm['preserved_source_coordinates'],
        retained_original_variables=c['retained_original_variables'],retained_original_rows=c['retained_original_rows'],
        actual_free_factored_coordinates=c['unconstrained_removed'],reverse_monic_restorations=list(reversed(c['steps'])),
        inverse_order=['initialize_every_actual_free_factored_coordinate','reverse_all_monic_steps','overwrite_original_Horn_private_witnesses','apply_sealed_source_ordinary_maps_and_calibration'],
        forward_order=['construct_complete_sealed_source_witness','overwrite_factored_Horn_private_witnesses','retain_projected_coordinates'],
        chart='identity; no translation or centering',old_private_witness_identity_claimed=False)

def materialize(destination, pinhash):
    safe(destination); need(not destination.exists() or not any(destination.iterdir()), 'destination must be empty')
    destination.mkdir(parents=True,exist_ok=True)
    # These are the only nonstdlib imports, after whole-file authentication.
    sys.path.insert(0,str(HERE/'vendor'))
    import terminal_elimination as E
    import factor_horn as F
    summary={}
    for name in PROFILES:
        folder=destination/name; folder.mkdir(); source=get(SOURCE/'data'/f'{name}.json')
        shutil.copyfile(SOURCE/'data'/f'{name}.json',folder/'source.json')
        factored,fc=F.transform(source)
        need(len(fc['changes'])==18 and fc['new_root']==len(source['variables']), 'fresh whole Horn certificate')
        projected,pc,engine=E.optimize(factored,max_support=16,affine_support=None,quadratic_first=False)
        receipt=E.verify(factored,projected,pc); poly=E.expand(projected); wm=horn_maps(E,source,factored,fc)
        values={'SOURCE_BINDING.json':source_binding(name),'factored_source.json':factored,
            'factorization_certificate.json':fc,'HORN_WITNESS_MAP.json':wm,'projected.json':projected,
            'terminal_elimination_certificate.json':pc,'ENGINE_VERIFICATION.json':receipt,
            'expanded_polynomial.json':poly,'METRICS.json':census(projected,poly),
            'COMPOSED_MAPS.json':composed(source,factored,pc,wm)}
        for n,x in values.items(): put(folder/n,x)
        endpoint=dict(schema='round16_raw_endpoint_binding_v1',profile=name,source_manifest_sha256=SOURCE_SEAL,
            source_pins_sha256=pinhash,all_prior_profile_files=inventory(folder),
            equivalence_chain=['complete_sealed_literal_source','fresh_Horn_existential_maps','fresh_integral_monic_and_free_coordinate_maps','full_literal_sum_of_squares'],
            source_restored_before_native_calibration=True,chart='raw untranslated',old_private_tuple_identity_claimed=False)
        put(folder/'ENDPOINT_BINDING.json',endpoint)
        summary[name]=dict(engine=engine,raw=census(projected,poly),actual_free_factored_coordinates=pc['unconstrained_removed'])
    index=dict(schema='round16_two_raw_projection_inventory_v1',source_pins_sha256=pinhash,
        producer_sha256=meta(HERE/'build.py')['sha256'],policy=POLICY,summary=summary,files=inventory(destination))
    put(destination/'INDEX.json',index); return index

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--check',action='store_true')
    p.add_argument('--destination',type=Path,default=HERE/'data'); p.add_argument('--output',type=Path,required=True)
    a=p.parse_args(); pinhash=authenticate(); safe(a.destination); safe(a.output,True)
    need(not (HERE/'MANIFEST.json').exists() or a.check, 'sealed data is immutable')
    if a.check:
        with tempfile.TemporaryDirectory(prefix='round16-projection-rebuild-') as td:
            scratch=Path(td)/'data'; index=materialize(scratch,pinhash)
            actual={str(q.relative_to(a.destination)):q.read_bytes() for q in a.destination.rglob('*') if q.is_file()}
            expected={str(q.relative_to(scratch)):q.read_bytes() for q in scratch.rglob('*') if q.is_file()}
            need(actual==expected,'whole deterministic raw-profile rebuild')
    else: index=materialize(a.destination,pinhash)
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),pure_check=a.check,
        source_pins_sha256=pinhash,index_sha256=sha(index),data_files=len(index['files'])+1,
        summary=index['summary'],scope='Exactly two raw F/E profiles; no translation, centering or global optimum claim.')
    out=(json.dumps(report,indent=2,sort_keys=True)+'\n').encode()
    need(not a.output.exists() or a.output.read_bytes()==out,'refuse changed receipt overwrite')
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_bytes(out); print(out.decode(),end='')
if __name__=='__main__': main()
