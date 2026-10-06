#!/usr/bin/env python3
"""Selected mathematical, schema, provenance and inventory regressions in private copies."""
import sys
sys.dont_write_bytecode=True
from hashlib import sha256
from pathlib import Path
import json
import shutil
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parent
class TestError(Exception):pass
def require(ok,message):
    if not ok:raise TestError(message)
def snapshot(root):
    return {p.relative_to(root).as_posix():('directory' if p.is_dir() else sha256(p.read_bytes()).hexdigest()) for p in root.rglob('*')}
def seal(root):
    (root/'manifest.sha256').write_text(''.join(sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n' for p in sorted(root.iterdir()) if p.is_file() and p.name!='manifest.sha256'),encoding='ascii')
def edit(path,value,name='evidence.json'):
    def mutate(root):
        p=root/name;d=json.loads(p.read_text());cursor=d
        for key in path[:-1]:cursor=cursor[key]
        cursor[path[-1]]=value;p.write_text(json.dumps(d,indent=2)+'\n');seal(root)
    return mutate
def source(old,new):
    def mutate(root):
        p=root/'verify.py';s=p.read_text();require(s.count(old)==1,'MUTATION: source target is not unique');p.write_text(s.replace(old,new));seal(root)
    return mutate
def duplicate(root):
    p=root/'evidence.json';s=p.read_text();p.write_text(s.replace('"schema":','"schema":"duplicate",\n  "schema":',1));seal(root)
def nonfinite(root):
    p=root/'evidence.json';s=p.read_text();p.write_text(s.replace('"direct_n": 8','"direct_n": NaN',1));seal(root)
def extra(root):(root/'payload.txt').write_text('unlisted\n')
def empty_directory(root):(root/'empty').mkdir()
def symlink(root):(root/'alias').symlink_to('evidence.json')
def unsealed(root):
    p=root/'evidence.json';p.write_text(p.read_text()+' ')
def missing(root):(root/'README.md').unlink()
def missing_manifest(root):
    p=root/'manifest.sha256';p.write_text('\n'.join(p.read_text().splitlines()[1:])+'\n')
def duplicate_manifest(root):
    p=root/'manifest.sha256';s=p.read_text();p.write_text(s+s.splitlines()[0]+'\n')
def bad_manifest(root):
    p=root/'manifest.sha256';p.write_text(p.read_text().replace('  ',' ',1))
CASES=[
 ('wrong_growth_759',edit(['classes','759','mu'],8),'MODEL: 759 critical parameters and identity'),
 ('wrong_growth_247',edit(['classes','247','mu'],9),'MODEL: 247 critical parameters and identity'),
 ('wrong_tilt_y',edit(['classes','247','y'],'1/2'),'MODEL: 247 critical parameters and identity'),
 ('wrong_class_sequence_identity',edit(['classes','759','oeis'],'A279551'),'MODEL: 759 critical parameters and identity'),
 ('wrong_staircase_center',edit(['classes','247','alpha'],'3/2'),'MODEL: 247 critical parameters and identity'),
 ('count_auxiliary_247_endpoints',edit(['classes','247','terminal_cap'],None),'MODEL: 247 terminal extraction'),
 ('truncate_759_terminals',edit(['classes','759','terminal_cap'],2),'MODEL: 759 terminal extraction'),
 ('759_mgf_b0_prefactor',edit(['classes','759','A','numerator','1,1'],'2'),'MGF: 759 joint identity b=0'),
 ('247_mgf_b0_missing_clock',edit(['classes','247','A','numerator'],{'1,0':'2','0,0':'1'}),'MGF: 247 joint identity b=0'),
 ('759_mgf_missing_duration_tilt',edit(['classes','759','R','numerator'],{'1,0':'4'}),'MGF: 759 joint identity b=1'),
 ('247_mgf_wrong_spatial_sign',edit(['classes','247','R','denominator','2,1'],'1'),'MGF: 247 joint identity b=1'),
 ('759_first_displacement_derivative',edit(['classes','759','critical','d_lambda_logR'],'1'),'CRITICAL: 759 d_lambda_logR'),
 ('247_first_displacement_derivative',edit(['classes','247','critical','d_lambda_logR'],'-1'),'CRITICAL: 247 d_lambda_logR'),
 ('759_second_displacement_derivative',edit(['classes','759','critical','d_lambda2_logR'],'3/4'),'CRITICAL: 759 d_lambda2_logR'),
 ('247_second_displacement_derivative',edit(['classes','247','critical','d_lambda2_logR'],'4/3'),'CRITICAL: 247 d_lambda2_logR'),
 ('759_duration_derivative',edit(['classes','759','critical','d_eta_logR'],'1'),'CRITICAL: 759 d_eta_logR'),
 ('247_duration_derivative',edit(['classes','247','critical','d_eta_logR'],'1'),'CRITICAL: 247 d_eta_logR'),
 ('759_boundary_killing',edit(['classes','759','critical','boundary_mass'],'1'),'CRITICAL: 759 boundary_mass'),
 ('247_boundary_killing',edit(['classes','247','critical','boundary_mass'],'2/3'),'CRITICAL: 247 boundary_mass'),
 ('247_cycle_prefactor',edit(['classes','247','factor_prefactor'],'3/8'),'CYCLE: 247 factor prefactor'),
 ('759_cycle_prefactor',edit(['classes','759','factor_prefactor'],'1/6'),'CYCLE: 759 factor prefactor'),
 ('fixed_terminal_tilt_direction',edit(['classes','759','endpoint_exponent'],1),'NORMALIZATION: 759 inverse endpoint tilt'),
 ('barrier_first_derivative',edit(['barrier','first_coefficients',1],'-1/2'),'BARRIER: first derivative algebra'),
 ('barrier_second_derivative',edit(['barrier','second_coefficients',2],'1/4'),'BARRIER: second derivative algebra'),
 ('barrier_spurious_cross_term',edit(['barrier','second_coefficients',1],'1/2'),'BARRIER: second derivative algebra'),
 ('inverse_lower_margin_direction',edit(['inverse','lower_margin_sign'],1),'INVERSE: strict margin directions'),
 ('inverse_upper_margin_direction',edit(['inverse','upper_margin_sign'],-1),'INVERSE: strict margin directions'),
 ('inverse_floor_instead_of_ceiling',edit(['inverse','lower_rounding'],'floor'),'INVERSE: ceiling directions'),
 ('inverse_negative_correction',edit(['inverse','correction_sign'],-1),'INVERSE: positive correction'),
 ('inverse_wrong_log_power',edit(['inverse','log_power'],'1'),'INVERSE: scale exponents'),
 ('incorrect_direct_coefficient',edit(['classes','759','counts',8],3207),'MODEL: 759 frozen internal counts'),
 ('incorrect_decorated_pair_count',edit(['classes','247','decorated_counts',8],10745),'DECORATED: 247 frozen pair counts'),
 ('incorrect_rigorous_floor',edit(['floor_samples',1,1],184206807539523655),'FLOOR: claimed exact samples'),
 ('first_return_omits_last_fulfillment',source('if c==1:out[w]=out.get(w,0)+count','if c==1:out[w]=out.get(w,0)+2*count'),'CYCLE: independent first return enumeration'),
 ('zero_commitment_has_bulk_duration',source('if b==0:return {0:1}','if b==0:return {1:1}'),'RENEWAL: 759 duration-resolved distribution'),
 ('247_multiplicity_off_by_one',source('def multiplicity(kind,ell,b):return catalan(b)*(choose(ell,b) if kind==759 else choose(b+1,ell-b))','def multiplicity(kind,ell,b):return catalan(b)*(choose(ell,b) if kind==759 else choose(b,ell-b))'),'CYCLE: 247 negative-binomial factorization'),
 ('boundary_cutoff_off_by_one',source('cap is None or b!=0 or h<cap','cap is None or b!=0 or h<cap-1'),'RENEWAL: 759 duration-resolved distribution'),
 ('tilted_fulfillment_omits_y',source('nxt[(p+1,c-1)]+=mass*F(x,mu)/y','nxt[(p+1,c-1)]+=mass*F(x,mu)'),'NORMALIZATION: propagated endpoint telescoping'),
 ('staircase_endpoint_shift',source('[(p,l+delta,pp),(pp,l-delta,p)]','[(p,l+delta+1,pp),(pp,l-delta,p)]'),'STAIRCASE: exact endpoint'),
 ('247_pending_word_ignores_000',source('|({(0,0,0)} if kind==247 else set())','|set()'),'DECORATED: full label distribution'),
 ('fill_excess_off_by_one',source('q,r=divmod(excess,2*R)','q,r=divmod(excess+1,2*R)'),'FILL: exact sum'),
 ('log_upper_tail_wrong_sign',source('return low,low+tail','return low,low-tail'),'FLOOR: certificate width'),
 ('noncanonical_rational',edit(['classes','759','y'],'2/4'),'SCHEMA: 759.y canonical rational'),
 ('boolean_range',edit(['ranges','direct_n'],True),'SCHEMA: ranges.direct_n integer'),
 ('boolean_count',edit(['classes','247','counts',0],True),'SCHEMA: 247.counts entry integer'),
 ('numeric_scope_boolean',edit(['scope','finite_only'],1),'SCHEMA: scope boolean'),
 ('unknown_nested_field',edit(['classes','247','critical','extra'],'1'),'SCHEMA: 247.critical keys'),
 ('unknown_root_field',edit(['extra'],1),'SCHEMA: evidence keys'),
 ('weakened_renewal_range',edit(['ranges','renewal_n'],23),'RANGE: mandatory coverage changed'),
 ('weakened_cutoff_range',edit(['cutoffs'],[2,4]),'RANGE: boundary cutoffs changed'),
 ('duplicate_json_key',duplicate,'JSON: duplicate key schema'),
 ('nonfinite_json_number',nonfinite,'JSON: nonfinite number'),
 ('zero_polynomial_term',edit(['classes','759','A','numerator','1,1'],'0'),'SCHEMA: polynomial zero term'),
 ('noncanonical_polynomial_power',edit(['classes','759','A','numerator'],{'01,1':'1'}),'SCHEMA: polynomial monomial'),
 ('false_all_size_certificate',edit(['scope','all_size_bounds_certified'],True),'SCOPE: analytic limitations'),
 ('false_effective_onset',edit(['scope','effective_onset'],True),'SCOPE: analytic limitations'),
 ('false_fitted_amplitude',edit(['scope','fitted_amplitudes'],True),'SCOPE: analytic limitations'),
 ('false_fresh_external_data',edit(['sequence_fixtures','fresh_external_retrieval'],True,'provenance.json'),'PROVENANCE: sequence fixture origin'),
 ('false_oeis_fixture',edit(['sequence_fixtures','external_fixtures'],['OEIS b279556.txt'],'provenance.json'),'PROVENANCE: sequence fixture origin'),
 ('wrong_primary_source_version',edit(['primary_source','version'],'arXiv:2512.21943v1','provenance.json'),'PROVENANCE: primary source'),
 ('wrong_proof_digest',edit(['analytic_sources','upper_proof'],'0'*64,'provenance.json'),'PROVENANCE: frozen analytic sources'),
 ('false_analytic_provenance',edit(['verification_scope'],'Finite proof of all asymptotics','provenance.json'),'PROVENANCE: analytic boundary'),
 ('unlisted_file',extra,'INVENTORY: unexpected or missing member'),
 ('unlisted_empty_directory',empty_directory,'INVENTORY: unexpected directory'),
 ('symlink',symlink,'INVENTORY: symlink forbidden'),
 ('unresealed_edit',unsealed,'HASH: evidence.json'),
 ('missing_file',missing,'INVENTORY: unexpected or missing member'),
 ('missing_manifest_entry',missing_manifest,'MANIFEST: closed inventory mismatch'),
 ('duplicate_manifest_entry',duplicate_manifest,'MANIFEST: duplicate member'),
 ('malformed_manifest',bad_manifest,'MANIFEST: malformed entry'),
]
def run(root,optimized,output=None):
    args=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(root/'verify.py')]
    if output is not None:args+=['--output',str(output)]
    return subprocess.run(args,cwd=root.parent,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
def main():
    require(len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=='--output'),'USAGE: python3 negative_tests.py [--output PATH]')
    output=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else None
    if output is not None:require(output!=ROOT and ROOT not in output.parents,'OUTPUT: path must be outside sealed checks directory')
    before=snapshot(ROOT);results=[];clean=[]
    with tempfile.TemporaryDirectory(prefix='report126-negative-') as td:
        temp=Path(td)
        for trial in range(2):
            for optimized in (False,True):
                copy=temp/('clean-'+str(trial)+'-'+str(optimized));shutil.copytree(ROOT,copy);saved=snapshot(copy)
                resultfile=temp/(copy.name+'.json');r=run(copy,optimized,resultfile)
                require(r.returncode==0 and r.stdout=='PASS: Report126 independent finite exact checks\n' and r.stderr=='','CLEAN: verifier did not pass')
                require(snapshot(copy)==saved,'CLEAN: source bytes or inventory changed')
                clean.append(resultfile.read_bytes())
        require(all(v==clean[0] for v in clean),'CLEAN: normal/optimized output disagreement')
        for name,mutate,diagnostic in CASES:
            for optimized in (False,True):
                copy=temp/(name+'-'+str(optimized));shutil.copytree(ROOT,copy);mutate(copy);saved=snapshot(copy)
                r=run(copy,optimized)
                require(r.returncode==1,'NEGATIVE: '+name+' exit '+str(r.returncode))
                require(r.stdout=='' and r.stderr=='FAIL: '+diagnostic+'\n','NEGATIVE: '+name+' diagnostic '+repr(r.stderr))
                require(snapshot(copy)==saved,'NEGATIVE: mutated copy changed')
            results.append({'case':name,'expected_diagnostic':diagnostic,'normal':'PASS','optimized':'PASS'})
        # A checker must refuse an in-tree output even if that name is already inventoried.
        for optimized in (False,True):
            copy=temp/('output-guard-'+str(optimized));shutil.copytree(ROOT,copy);saved=snapshot(copy)
            r=run(copy,optimized,copy/'evidence.json')
            require(r.returncode==1 and r.stderr=='FAIL: OUTPUT: path must be outside sealed checks directory\n','OUTPUT: active refusal')
            require(snapshot(copy)==saved,'OUTPUT: overwritten sealed member')
    require(snapshot(ROOT)==before,'IMMUTABILITY: original source bytes or inventory changed')
    result={'schema':'commitment-scale-negative-v1','status':'PASS','selected_mutations':len(results),'normal_and_optimized_mutation_runs':2*len(results),'clean_copy_replays':4,'all_clean_results_byte_identical':True,'output_guard_runs':2,'original_and_copy_inventories_unchanged':True,'cases':results,'limitations':'Selected regressions do not prove software correctness or any all-size analytic statement'}
    encoded=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if output is not None:output.write_text(encoded,encoding='utf-8')
    print('PASS: '+str(len(results))+' selected mutations in normal and optimized Python; four immutable clean replays')
if __name__=='__main__':
    try:main()
    except TestError as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
