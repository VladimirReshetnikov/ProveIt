#!/usr/bin/env python3
"""Negative controls: intentional diagnostics, executed normally and under -O.

Mutants live in temporary directories outside the closed checks inventory. For
semantic mutations, hashes are deliberately resealed to test mathematics/schema,
not merely to trip a stale checksum. No assert statement is used for validation.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode=True
import exact as e
import verify as v

def reseal(root):
    files={}
    for name in v.INVENTORY:
        if name!='inventory.json':
            data=(root/name).read_bytes(); files[name]={'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
    (root/'inventory.json').write_text(json.dumps({'schema_version':1,'files':files},indent=2,sort_keys=True)+'\n')

def edit_fixture(root,fn):
    f=json.loads((root/'fixtures.json').read_text()); fn(f)
    (root/'fixtures.json').write_text(json.dumps(f,indent=2,sort_keys=True)+'\n'); reseal(root)

def replace_code(root,name,old,new):
    text=(root/name).read_text(); e.need(old in text,'MUTATION_TARGET_MISSING',old)
    (root/name).write_text(text.replace(old,new,1)); reseal(root)

def duplicate(root):
    p=root/'fixtures.json'; p.write_text(p.read_text().replace('{','{"schema_version":1,',1)); reseal(root)

def alter_manifest(root):
    p=root/'inventory.json'; f=json.loads(p.read_text()); f['files']['exact.py']['sha256']='0'*64; p.write_text(json.dumps(f))

def run_one(root,opt,script=None):
    args=[sys.executable]+(['-O'] if opt else [])+(['-c',script] if script else ['verify.py'])
    result=subprocess.run(args,cwd=root,text=True,capture_output=True,timeout=180)
    e.need(not result.stderr,'MUTATION_STDERR',result.stderr)
    try: out=json.loads(result.stdout)
    except ValueError: raise e.Failure('MUTATION_NON_JSON',result.stdout[:300]) from None
    return result.returncode,out

def direct_script(expression):
    return "import sys,json; sys.dont_write_bytecode=True; import exact as e\ntry:\n "+expression+"\n print(json.dumps({'status':'PASS'}))\nexcept e.Failure as ex:\n print(json.dumps({'status':'FAIL','diagnostic':ex.code})); sys.exit(1)\n"

def run():
    v.integrity(); v.load_fixture()
    controls=[
      ('extra_file',lambda r:(r/'unexpected.txt').write_text('x'),'INVENTORY_UNEXPECTED_OR_MISSING',None),
      ('missing_file',lambda r:(r/'README.md').unlink(),'INVENTORY_UNEXPECTED_OR_MISSING',None),
      ('payload_truncation',lambda r:(r/'README.md').write_text('truncated'),'INVENTORY_SIZE_MISMATCH',None),
      ('manifest_hash',alter_manifest,'INVENTORY_HASH_MISMATCH',None),
      ('unknown_fixture_key',lambda r:edit_fixture(r,lambda f:f.update(unexpected=True)),'FIXTURE_SCHEMA',None),
      ('duplicate_fixture_key',duplicate,'FIXTURE_JSON_DUPLICATE_KEY',None),
      ('boolean_schema_version',lambda r:edit_fixture(r,lambda f:f.update(schema_version=True)),'FIXTURE_VERSION',None),
      ('lowered_range',lambda r:edit_fixture(r,lambda f:f['ranges'].update(interlacing_n_max=2)),'FIXTURE_RANGES',None),
      ('noncanonical_fraction',lambda r:edit_fixture(r,lambda f:f['ell_at_3'].update({'1':'2/8'})),'FIXTURE_ELL_VALUE_CANONICAL',None),
      ('wrong_ell_fixture',lambda r:edit_fixture(r,lambda f:f['ell_at_3'].update({'1':'1/3'})),'FIXTURE_ELL_MATH',None),
      ('symbolic_coefficient',lambda r:replace_code(r,'exact.py','b=lambda z:2*z**3+3*(a+1)*z**2','b=lambda z:2*z**3+4*(a+1)*z**2'),'SYMBOLIC_COMMUTATOR',None),
      ('corner_deletion_shift',lambda r:replace_code(r,'verify.py','corner={mask>>1:c','corner={mask>>2:c'),'CORNER_DELETION',None),
      ('original_kernel_coefficient',lambda r:replace_code(r,'exact.py','return (t if r==s==0 else 0)+sum','return (2*t if r==s==0 else 0)+sum'),'KERNEL_ORIGINAL_ENTRY',None),
      ('determinant_derivative_scale',lambda r:replace_code(r,'exact.py','return sum(determinant([[b[i][j]','return 2*sum(determinant([[b[i][j]'),'PFAFFIAN_ADJACENT_DERIVATIVE',None),
      ('toeplitz_trace_coefficient',lambda r:replace_code(r,'verify.py','r=[F(1,2)]+','r=[F(1,3)]+'),'CALIBRATION_TRACE',None),
      ('singular_trace_sign',lambda r:replace_code(r,'verify.py','F((-1)**(i-j))','F(1)'),'SINGULAR_TRACE_DECOMPOSITION',None),
      ('rational_reciprocal_trace',lambda r:replace_code(r,'exact.py','trace(Q)==F(n,2)','trace(Q)==F(n,3)'),'RECIPROCAL_TRACE',direct_script('e.rational_matrices(2,e.F(2))')),
      ('rational_factorization',lambda r:replace_code(r,'exact.py','F(comb(j,i)) if j>=i','F(comb(j,i)+1) if j>=i'),'RATIONAL_CHOLESKY',direct_script('e.rational_matrices(2,e.F(2))')),
      ('rational_commutator',lambda r:replace_code(r,'exact.py','F((i+a)*f(i))','F((i+a+1)*f(i))'),'RATIONAL_COMMUTATOR',direct_script('e.rational_matrices(2,e.F(2))')),
      ('symbolic_conjugation',lambda r:replace_code(r,'exact.py','c=(a+1)*(N-a-1)','c=(a+1)*(N-a-2)'),'SYMBOLIC_CONJUGATION',direct_script('e.arbitrary_parameter_identities()')),
      ('minus_product_scale',lambda r:replace_code(r,'exact.py','def minus_J(m): return F(factorial(m))','def minus_J(m): return 2*F(factorial(m))'),'ROSENGREN_MINUS_EVEN',None),
      ('plus_product_scale',lambda r:replace_code(r,'exact.py','return 2*factorial(m)*rising','return 3*factorial(m)*rising'),'ROSENGREN_PLUS',None),
      ('ratio_product_scale',lambda r:replace_code(r,'verify.py','ratios[m]/ratios[m-1]==9*','ratios[m]/ratios[m-1]==8*'),'ROSENGREN_RATIO',None),
      ('stirling_coefficient_sign',lambda r:replace_code(r,'exact.py','sign*(-1)**(k+1)*bernoulli_polynomial','sign*(-1)**k*bernoulli_polynomial'),'STIRLING_COEFFICIENTS',direct_script('e.stirling()')),
      ('incorrect_integral_sign',lambda r:replace_code(r,'exact.py','partial=F(1,2)*den-2*(1+2*y)','partial=F(1,2)*den+2*(1+2*y)'),'INTEGRAL_PARTIAL_FRACTIONS',direct_script('e.integral_algebra()')),
      ('nonreal_root_control',lambda r:None,'NONREAL_ROOT',direct_script('e.interlaces([1,0,1],[0,1])')),
      ('noninterlacing_control',lambda r:None,'INTERLACING_ORDER',direct_script('e.interlaces([0,-1,0,1],[-4,0,1])')),
      ('unmatched_multiple_root',lambda r:None,'INTERLACING_REDUCED_MULTIPLICITY',direct_script('e.interlaces([1,-2,1],[1,1])')),
      ('pressure_mean_sign',lambda r:replace_code(r,'pressure.py','F(1,2)-1/((s+1)*(s+2))','F(1,2)+1/((s+1)*(s+2))'),'PRESSURE_MEAN',direct_script('__import__(\'pressure\').algebra()')),
      ('pressure_resolvent_sign',lambda r:replace_code(r,'pressure.py','rhs=-2/((s-1)*(3*w+1))','rhs=2/((s-1)*(3*w+1))'),'PRESSURE_RESOLVENT_PARTIAL_FRACTIONS',direct_script('__import__(\'pressure\').algebra()')),
      ('pressure_factorization_scale',lambda r:replace_code(r,'pressure.py','e.inverse(B)),3*delta)','e.inverse(B)),2*delta)'),'PRESSURE_FINITE_ORDERED_FACTORIZATION',direct_script('__import__(\'pressure\').finite(__import__(\'verify\').RANGES)')),
      ('pressure_pole_determinant',lambda r:replace_code(r,'pressure.py','e.determinant(M)/2**n==original','e.determinant(M)/3**n==original'),'PRESSURE_FINITE_POLE_CLEARING',direct_script('__import__(\'pressure\').finite(__import__(\'verify\').RANGES)')),
      ('pressure_path_sum_scale',lambda r:replace_code(r,'pressure.py','total+=states.get(start,F(0))','total+=2*states.get(start,F(0))'),'PRESSURE_MIXED_PATH_IDENTITY',direct_script('__import__(\'pressure\').finite(__import__(\'verify\').RANGES)')),
      ('pressure_symbol_coefficient',lambda r:replace_code(r,'pressure.py','b=[0,-1,0,2]','b=[0,-2,0,2]'),'PRESSURE_SYMBOL_MOMENT',direct_script('__import__(\'pressure\').finite(__import__(\'verify\').RANGES)')),
      ('pressure_jacobi_profile',lambda r:replace_code(r,'pressure.py','lead(diagonal)-(2*x**3-x)','lead(diagonal)-(3*x**3-x)'),'PRESSURE_JACOBI_DIAGONAL_PROFILE',direct_script('__import__(\'pressure\').finite(__import__(\'verify\').RANGES)')),
      ('pressure_stieltjes_sign',lambda r:replace_code(r,'pressure.py','+3/(s*(s*s-1)*(s*s-4))','-3/(s*(s*s-1)*(s*s-4))'),'PRESSURE_STIELTJES_TRANSFORM',direct_script('__import__(\'pressure\').algebra()')),
      ('ldp_saddle_coefficient',lambda r:replace_code(r,'pressure.py','1+8/(1-2*mean)','1+7/(1-2*mean)'),'LDP_SADDLE_DISCRIMINANT',direct_script('__import__(\'pressure\').corollaries()')),
      ('threshold_quadratic_sign',lambda r:replace_code(r,'pressure.py','root=(d-r)/(2*alpha)','root=(d+r)/(2*alpha)'),'THRESHOLD_QUADRATIC_ROOT',direct_script('__import__(\'pressure\').corollaries()')),
      ('pressure_density_mass',lambda r:replace_code(r,'pressure.py','mass=6/((w+1)*(w+4))','mass=5/((w+1)*(w+4))'),'PRESSURE_DENSITY_MASS_PARTIAL_FRACTIONS',direct_script('__import__(\'pressure\').algebra()')),
      ('zero_polynomial_divisor',lambda r:None,'POLY_DIV_ZERO',direct_script('e.divmodp([1],[0])')),
      ('sturm_root_endpoint',lambda r:None,'STURM_ENDPOINT_ROOT',direct_script('e.root_count(e.sturm([0,1]),0,1)')),
    ]
    e.need(len(controls)==41,'MUTATION_CAMPAIGN_SIZE')
    cases=[]
    with tempfile.TemporaryDirectory(prefix='report121-mutations-') as td:
        base=Path(td)
        # Execute the complete unmodified verifier in both interpreter modes.
        for opt in [False,True]:
            rc,out=run_one(v.ROOT,opt)
            e.need(rc==0 and out.get('status')=='PASS','MUTATION_BASELINE',str(out))
        for name,mutate,want,script in controls:
            for opt in [False,True]:
                root=base/(name+('-O' if opt else '-normal')); shutil.copytree(v.ROOT,root)
                mutate(root); rc,out=run_one(root,opt,script)
                e.need(rc==1 and out.get('status')=='FAIL' and out.get('diagnostic')==want,'MUTATION_WRONG_DIAGNOSTIC',f'{name}, -O={opt}: rc={rc}, {out}')
                cases.append({'case':name,'optimized':opt,'diagnostic':want})
    e.need(len(cases)==82,'MUTATION_RUN_COUNT')
    return {'status':'PASS','baseline_modes':['normal','-O'],'negative_cases':len(cases),'all_failures_intentional':True,'cases':cases}

def main():
    try: print(json.dumps(run(),sort_keys=True,indent=2)); return 0
    except e.Failure as ex: print(json.dumps({'status':'FAIL','diagnostic':ex.code,'detail':ex.detail},sort_keys=True)); return 1
    except Exception as ex: print(json.dumps({'status':'ERROR','diagnostic':'UNEXPECTED_EXCEPTION','detail':type(ex).__name__+': '+str(ex)},sort_keys=True)); return 2
if __name__=='__main__': sys.exit(main())
