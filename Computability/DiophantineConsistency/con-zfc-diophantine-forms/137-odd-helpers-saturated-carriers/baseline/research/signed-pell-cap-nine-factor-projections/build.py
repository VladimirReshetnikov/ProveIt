#!/usr/bin/env python3
"""Fused-nine two-chart compiler; CODE ONLY/HOLD for both full reviews."""
import argparse,contextlib,copy,hashlib,io,json,shutil,sys,tempfile
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/'research/signed-pell-cap-nine-factor-source'
SOURCE_SEAL='845bc6642212eb600d2f0ecf663cb805a6e1989b63faf7087d44142e5cc75190'
SOURCE_FILES=['source.json','guarded.json','domain.json','TRANSFORM.json','CALIBRATION_BINDING.json']
BASELINES=[('cap_plain','research/signed-pell-cap-projections','data/plain'),
 ('cap_centered','research/signed-pell-cap-projections','data/centered'),
 ('grouped_centered','research/signed-pell-cap-grouped-quartic','data'),
 ('helper_plain','research/round15-helper-guard-projections','full-data/joint_helper/plain'),
 ('helper_centered','research/round15-helper-guard-projections','full-data/joint_helper/centered'),
 ('product_plain','research/signed-pell-cap-refined-product-projections','data/plain'),
 ('product_centered','research/signed-pell-cap-refined-product-projections','data/centered')]
POLICY=dict(max_support=16,affine_support=None,quadratic_first=False,charts=['plain','centered'],private_slack_pruning=False)
def need(ok,why):
    if not ok:raise ValueError(why)
def get(p):return json.loads(p.read_bytes())
def canon(d):return (json.dumps(d,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(b):return hashlib.sha256(b).hexdigest()
def sha(d):return digest(canon(d))
def put(p,d):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(canon(d))
def inventory(p):return {str(q.relative_to(p)):digest(q.read_bytes()) for q in sorted(p.rglob('*')) if q.is_file() and str(q.relative_to(p))!='INDEX.json'}
def authenticate():
    pins=get(HERE/'SOURCE_PINS.json')
    for n,h in pins['files'].items():need(digest((ROOT/n).read_bytes())==h,'whole input '+n)
    for n,h in pins['vendor'].items():need(digest((HERE/'vendor'/n).read_bytes())==h,'whole vendor '+n)
    for n,h in pins['core'].items():need(digest((HERE/n).read_bytes())==h,'whole author core '+n)
    for n,h in pins['closed_dependencies'].items():
        folder=ROOT/n;need(digest((folder/'MANIFEST.json').read_bytes())==h,'closed dependency pin '+n)
        declared=get(folder/'MANIFEST.json')['files'];actual={str(q.relative_to(folder)):digest(q.read_bytes()) for q in folder.rglob('*') if q.is_file() and q!=folder/'MANIFEST.json'}
        expected={name:dict(bytes=(folder/name).stat().st_size,sha256=value) if isinstance(declared.get(name),dict) else value for name,value in actual.items()}
        need(declared==expected,'closed whole dependency, hashes and byte counts '+n)
    need(digest((SOURCE/'MANIFEST.json').read_bytes())==SOURCE_SEAL,'accepted complete fused-nine source')
    if (HERE/'MANIFEST.json').exists():
        actual={str(q.relative_to(HERE)):digest(q.read_bytes()) for q in HERE.rglob('*') if q.is_file() and q!=HERE/'MANIFEST.json'}
        need(get(HERE/'MANIFEST.json')['files']==actual,'whole closed author packet')
    return digest((HERE/'SOURCE_PINS.json').read_bytes())
def protected(path):
    return any(path.resolve().is_relative_to((ROOT/n).resolve()) for n in get(HERE/'SOURCE_PINS.json')['closed_dependencies'])
def horn_maps(E,src,dst,c):
    """Emit actual private-witness overwrite rules, not an all-coordinate identity."""
    oldrows=[E.normalize(r['terms']) for r in src['residuals']];newrows=[E.normalize(r['terms']) for r in dst['residuals']]
    sq=c['square_variables'];g=c['guard_variables'];deleted=set(c['deleted_rows']);rm={i:j for j,i in enumerate(i for i in range(len(oldrows)+1) if i not in deleted)}
    defs={s:next(i for i,r in enumerate(src['residuals']) if r['label']=='nonnegative_square_difference' and oldrows[i].get((s,))==1) for s in sq}
    h,u,z,d=(g[k] for k in ['h','old_second_square','g','old_D_square'])
    product=E.multiply({(h,):1},{(u,):1})
    pr=next(i for i,p in enumerate(oldrows) if E.candidate(p,z,False)==product)
    dr=next(i for i,p in enumerate(oldrows) if E.candidate(p,d,False) is not None)
    old_defs={s:defs[s] for s in sq[:9]+sq[13:15]+[h,u,sq[11]]};old_defs.update({z:pr,d:dr});old_defs.update({v:r for r,v in c['product_chain']})
    new_defs={v:rm[r] for v,r in old_defs.items() if v not in {u,d}};new_defs[c['new_root']]=len(newrows)-1
    def ordered(definitions,rows):
        todo={v:(r,E.candidate(rows[r],v,False)) for v,r in definitions.items()};need(all(f is not None for r,f in todo.values()),'all Horn witness rows monic')
        rules=[]
        while todo:
            choices=[v for v,(r,f) in todo.items() if not {j for m in f for j in m}&set(todo)];need(choices,'acyclic Horn witness rebuild')
            v=min(choices);r,f=todo.pop(v);rules.append(dict(coordinate=v,row=r,restoration=E.as_terms(f)))
        return rules
    private=sorted(old_defs);forward=ordered(new_defs,newrows);reverse=ordered(old_defs,oldrows)
    return dict(schema='signed_cap_horn_existential_maps_v1',source_sha256=sha(src),factored_sha256=sha(dst),preserved_source_coordinates=sorted(set(range(len(src['variables'])))-set(private)),overwritten_source_coordinates=private,
        source_to_factored=dict(copy_source_coordinates=list(range(len(src['variables']))),initialize_factored_private_to_zero=sorted({u,d}),restorations=forward),
        factored_to_source=dict(discard_factored_coordinates=[c['new_root']],copy_source_coordinates=list(range(len(src['variables']))),restorations=reverse),
        full_old_witness_identity_claimed=False,projection_free_coordinates='Use every actual unconstrained_removed coordinate, without assuming its cardinality. Initialize it to zero for the factored chart, then apply the reverse Horn overwrite rules for an old-source witness.',
        identity_scope='Monic projection identities hold relative to the factored residual ideals. Horn maps preserve the listed exposed coordinates and reconstruct private witnesses in each direction; the maps need not be inverse on old private witnesses.')
def census(eq,p):return dict(variables=len(eq['variables']),rows=len(eq['residuals']),degree=max((len(m) for c,m in p['terms']),default=0),monomials=len(p['terms']),height=max((abs(c) for c,m in p['terms']),default=0),row_height=max((abs(c) for r in eq['residuals'] for c,m in r['terms']),default=0))
def normalized_baseline(alias,raw):
    if alias!='grouped_centered':return raw
    return dict(variables=raw['declared_variables'],rows=raw['residuals'],degree=raw['degree'],monomials=raw['terms'],height=raw['height'],row_height=raw['residual_height'])
def materialize(out,pinhash):
    need(not protected(out) and not out.is_symlink(),'never write closed dependencies or symlink destinations')
    need(not out.exists() or not any(out.iterdir()),'destination must be empty');out.mkdir(parents=True,exist_ok=True)
    # No executable parent module is imported. The seven exact local vendor
    # files are the complete reviewed runtime closure, loaded only after pins.
    sys.path.insert(0,str(HERE/'vendor'))
    import terminal_elimination as E
    import factor_horn as F
    import translate_coordinates as T
    import center_integer as C
    for n in SOURCE_FILES:shutil.copyfile(SOURCE/n,out/n)
    guarded=get(SOURCE/'guarded.json');factored,fc=F.transform(guarded);need(len(fc['changes'])==18,'exact accepted Horn edit set')
    projected,pc,metrics=E.optimize(factored,max_support=16);receipt=E.verify(factored,projected,pc)
    wm=horn_maps(E,guarded,factored,fc)
    binding=dict(schema='fused_nine_projection_source_binding_v1',source_manifest_sha256=SOURCE_SEAL,
        whole_literal_artifacts={n:digest((SOURCE/n).read_bytes()) for n in SOURCE_FILES},ordinary_manifest_sha256=get(SOURCE/'source.json')['ordinary_manifest_sha256'],
        source_calibration=get(SOURCE/'CALIBRATION_BINDING.json'),single_fused_nine_policy=True,whole_parent_body_coordinates_fixed=406,whole_parent_body_rows_fixed=341,
        BOTH_old_graph_triples_freshly_rechosen=True,F_A_C_V_d_and_endpoint_signs_not_reintroduced=True,old_private_slack_pruning_applied=False,private_Pell_tuple_identity_to_baselines_claimed=False)
    for n,d in [('SOURCE_BINDING.json',binding),('factored_source.json',factored),('factorization_certificate.json',fc),('HORN_WITNESS_MAP.json',wm),('projected.json',projected),('terminal_elimination_certificate.json',pc),('ENGINE_VERIFICATION.json',receipt)]:put(out/n,d)
    shifts={i:(-16 if v['name']=='t0' else -1) for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'] in ('t0','M0') or v['name'].endswith('minus1')}
    plain=T.translate(projected,shifts);poly=E.expand(plain);tc=dict(schema='integral_translation_v1',input_sha256=sha(projected),output_sha256=sha(plain),shifts=[[i,s] for i,s in shifts.items()],convention='old=new+shift')
    for n,d in [('equation.json',plain),('expanded_polynomial.json',poly),('translation_certificate.json',tc),('METRICS.json',census(plain,poly)),('projected.json',projected)]:put(out/'plain'/n,d)
    transcript=io.StringIO()
    with contextlib.redirect_stdout(transcript):C.center(out/'plain',out/'centered')
    put(out/'CENTER_SEARCH.json',dict(transcript=transcript.getvalue(),scope='Exact accepted finite coordinate-descent policy; no global optimum claim.'))
    comparison={}
    for alias,directory,relative in BASELINES:
        folder=ROOT/directory/relative;raw=get(folder/'METRICS.json');old=normalized_baseline(alias,raw)
        comparison[alias]=dict(parent_directory=directory,parent_manifest_sha256=digest((ROOT/directory/'MANIFEST.json').read_bytes()),relative_directory=relative,
            complete_baseline_files={n:digest((folder/n).read_bytes()) for n in ['equation.json','expanded_polynomial.json','METRICS.json']},
            literal_baseline_metrics=raw,normalized_metrics=old,charts={chart:dict(new_metrics=get(out/chart/'METRICS.json'),delta={k:get(out/chart/'METRICS.json')[k]-old[k] for k in old}) for chart in ['plain','centered']})
    put(out/'COMPARISON.json',dict(schema='fused_nine_complete_alternatives_v1',source_manifest_sha256=SOURCE_SEAL,baselines=comparison,
        polynomial_identity_claimed=False,old_private_Pell_tuple_identity_claimed=False,scope='Complete calibrated cap, grouped cap, helper and eight-factor product charts; numerical differences only, no private tuple or polynomial identity.'))
    maps=dict(schema='fused_nine_composed_integer_maps_v1',source_coordinates=len(guarded['variables']),factored_coordinates=len(factored['variables']),
        source_to_factored=wm['source_to_factored'],factored_to_source=wm['factored_to_source'],Horn_preserved_source_coordinates=wm['preserved_source_coordinates'],
        projection_retained_original_variables=pc['retained_original_variables'],projection_retained_original_rows=pc['retained_original_rows'],
        actual_projection_free_coordinates=pc['unconstrained_removed'],reverse_monic_restorations=list(reversed(pc['steps'])),
        charts={chart:dict(integer_domain='unrestricted integers',convention='projected_old=chart_new+shift',shifts=get(out/chart/'translation_certificate.json')['shifts'],
                           chart_coordinate_metadata=get(out/chart/'equation.json')['variables']) for chart in ['plain','centered']},
        inverse_order=['inverse_integer_translation','assign_every_actual_free_coordinate_zero','reverse_all_monic_restorations','overwrite_original_Horn_private_witnesses','apply_sealed_source_calibration'],
        forward_order=['construct_sealed_source_witness','overwrite_factored_Horn_private_witnesses','retain_actual_projected_coordinates','subtract_integer_translation'],
        whole_old_Horn_private_tuple_identity_claimed=False)
    put(out/'COMPOSED_MAPS.json',maps)
    endpoint=dict(schema='fused_nine_complete_endpoint_calibration_v1',source_manifest_sha256=SOURCE_SEAL,
        ordinary_manifest_sha256=get(SOURCE/'source.json')['ordinary_manifest_sha256'],source_calibration_sha256=digest((SOURCE/'CALIBRATION_BINDING.json').read_bytes()),
        source_pins_sha256=pinhash,all_prior_generated_files=inventory(out),
        equivalence_chain=['sealed_fused_nine_source_calibration','actual_Horn_existential_maps','actual_monic_and_free_coordinate_maps','integer_chart_bijections','full_literal_sum_of_squares'],
        reconstructed_source_is_whole_guarded_tuple=True,native_calibration_applied_only_after_full_source_restoration=True,
        all_source_product_frame_and_sign_interfaces_unchanged=True,new_unbounded_or_Lean_theorem_claimed=False)
    put(out/'ENDPOINT_BINDING.json',endpoint)
    summary=dict(engine=metrics,plain=census(plain,poly),centered=get(out/'centered/METRICS.json'))
    index=dict(schema='fused_nine_two_chart_projection_inventory_v1',source_pins_sha256=pinhash,policy=POLICY,summary=summary,files=inventory(out));put(out/'INDEX.json',index);return index
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');p.add_argument('--destination',type=Path,default=HERE/'data');p.add_argument('--output',type=Path,required=True);a=p.parse_args();pinhash=authenticate()
    need(not protected(a.destination) and not protected(a.output),'never write closed dependencies')
    need(not (HERE/'MANIFEST.json').exists() or a.check,'sealed generated data is immutable')
    if a.check:
        with tempfile.TemporaryDirectory(prefix='signed-cap-projection-rebuild-') as td:
            scratch=Path(td)/'data';index=materialize(scratch,pinhash)
            need({str(q.relative_to(scratch)):q.read_bytes() for q in scratch.rglob('*') if q.is_file()}=={str(q.relative_to(a.destination)):q.read_bytes() for q in a.destination.rglob('*') if q.is_file()},'whole deterministic generated inventory')
    else:index=materialize(a.destination,pinhash)
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),pure_check=a.check,index_sha256=sha(index),source_pins_sha256=pinhash,summary=index['summary'],files=len(index['files']),scope='Exact one-policy Horn/projection/translation charts at the completely calibrated fused-nine source. No global optimality claim.')
    text=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode();need(not a.output.is_symlink() and (not a.output.exists() or a.output.read_bytes()==text),'refuse changed receipt overwrite')
    need(not (HERE/'MANIFEST.json').exists() or not a.output.resolve().is_relative_to(HERE),'receipt outside sealed packet');a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(text);print(text.decode(),end='')
if __name__=='__main__':main()
