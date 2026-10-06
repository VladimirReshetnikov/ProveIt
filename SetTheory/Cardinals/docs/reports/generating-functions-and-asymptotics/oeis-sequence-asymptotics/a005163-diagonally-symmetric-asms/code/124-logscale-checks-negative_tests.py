#!/usr/bin/env python3
"""Selected adversarial controls, using clean temporary copies and exact failures."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode=True
from algebra import Failure, require
ROOT=Path(__file__).resolve().parent

def snapshot(root):
    return {str(p.relative_to(root)):{'bytes':len(p.read_bytes()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(root.rglob('*')) if p.is_file()}

def seal(root):
    files={name:{'bytes':len((root/name).read_bytes()),'sha256':hashlib.sha256((root/name).read_bytes()).hexdigest()} for name in ['README.md','algebra.py','fixtures.json','negative_tests.py','verify.py']}
    (root/'inventory.json').write_text(json.dumps({'schema_version':1,'files':files},indent=2,sort_keys=True)+'\n')

def change_json(root,path,fn):
    p=root/path; value=json.loads(p.read_text()); fn(value); p.write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')

def source_change(root,old,new):
    p=root/'algebra.py'; content=p.read_text()
    require(content.count(old)==1,'NEGATIVE_MUTATION_ANCHOR',old)
    p.write_text(content.replace(old,new))

def source_case(name,code,old,new): return (name,code,lambda root:source_change(root,old,new),True)
def fixture_case(name,code,fn): return (name,code,lambda root:change_json(root,'fixtures.json',fn),True)

def run_copy(root,optimized):
    before=snapshot(root)
    proc=subprocess.run([sys.executable]+(['-O'] if optimized else [])+[str(root/'verify.py')],cwd=root.parent,capture_output=True,text=True)
    after=snapshot(root)
    require(before==after,'NEGATIVE_RUN_CHANGED_BYTES')
    require(not proc.stderr,'NEGATIVE_UNEXPECTED_STDERR',proc.stderr[:300])
    try: result=json.loads(proc.stdout)
    except ValueError: raise Failure('NEGATIVE_INVALID_JSON',proc.stdout[:300]) from None
    return proc.returncode,result

def cases():
    out=[
        ('extra-file','INVENTORY_UNEXPECTED_OR_MISSING',lambda r:(r/'unlisted.txt').write_text('extra'),False),
        ('missing-file','INVENTORY_UNEXPECTED_OR_MISSING',lambda r:(r/'README.md').unlink(),False),
        ('inventory-version-boolean','INVENTORY_VERSION',lambda r:change_json(r,'inventory.json',lambda f:f.update(schema_version=True)),False),
        ('inventory-unknown-field','INVENTORY_SCHEMA',lambda r:change_json(r,'inventory.json',lambda f:f.update(extra=1)),False),
        ('unsealed-byte-change','INVENTORY_HASH_MISMATCH',lambda r:(r/'README.md').write_bytes((r/'README.md').read_bytes().replace(b'report124',b'report125',1)),False),
        ('unsealed-size-change','INVENTORY_SIZE_MISMATCH',lambda r:(r/'README.md').write_text((r/'README.md').read_text()+'\n'),False),
        ('fixture-duplicate-key','FIXTURE_JSON_DUPLICATE_KEY',lambda r:(r/'fixtures.json').write_text((r/'fixtures.json').read_text().replace('"report": "report124"','"report": "report124", "report": "report124"')),True),
        fixture_case('fixture-version-boolean','FIXTURE_VERSION',lambda f:f.update(schema_version=True)),
        fixture_case('fixture-unknown-field','FIXTURE_SCHEMA',lambda f:f.update(extra=1)),
        fixture_case('weakened-ranges','FIXTURE_RANGES',lambda f:f['ranges'].update(hahn_degree_max=3)),
        fixture_case('range-nested-boolean','FIXTURE_RANGES',lambda f:f['ranges']['projection_dimensions'][0].__setitem__(1,True)),
        fixture_case('public-source-provenance','FIXTURE_PROVENANCE',lambda f:f['provenance'].update(continuous_Hahn='unattributed')),
        fixture_case('historical-report-relabel','HISTORICAL_PROVENANCE',lambda f:f['historical']['provenance'].update(source_report='report124')),
        fixture_case('historical-hash-change','HISTORICAL_PROVENANCE',lambda f:f['historical']['provenance'].update(source_file_sha256='0'*64)),
        fixture_case('historical-rational-noncanonical','HISTORICAL_DERIVATIVE_VALUE_CANONICAL',lambda f:f['historical']['ell_at_3'].update({'1':'2/8'})),
        fixture_case('historical-count-boolean','HISTORICAL_SMALL_Z_VALUE',lambda f:f['historical']['small_z']['0'].__setitem__(0,True)),
        fixture_case('historical-count-math','INHERITED_SMALL_Z_MATH',lambda f:f['historical']['small_z']['6'].__setitem__(0,27)),
        fixture_case('historical-derivative-math','INHERITED_DERIVATIVE_MATH',lambda f:f['historical']['ell_at_3'].update({'3':'31/56'})),
        fixture_case('analytic-limit-overclaim','FIXTURE_LIMITATIONS',lambda f:f['limitations'].__setitem__(0,'Finite checks certify the uniform O(1) remainder.')),
        source_case('original-kernel-sign','ORIGINAL_KERNEL_COEFFICIENT','G[i][j]-=B[i-k-1][j-k]','G[i][j]+=B[i-k-1][j-k]'),
        source_case('adjacent-size-index','ADJACENT_DETERMINANT','D==peval(p[n],t)*peval(p[n+1],t)','D==peval(p[n],t)*peval(p[n],t)'),
        source_case('ASM-calibration-factor','ASM_PRODUCT_CALIBRATION','D==2**n*asm','D==3**n*asm'),
        source_case('Stirling-B2-constant','CALIBRATION_STIRLING_LOG_POWER','d*d-d+F(1,6)','d*d-d+F(1,5)'),
        source_case('Hahn-recurrence-denominator','HAHN_JACOBI_NORM_RATIO','4*(2*n+1)*(2*n+3)','5*(2*n+1)*(2*n+3)'),
        source_case('Hahn-hypergeometric-parameter','HAHN_REAL_PARITY','F(5,6)+k-1','F(7,6)+k-1'),
        source_case('Fourier-phase-sign','FOURIER_JACOBI_PHASE','pscale(polys[n],(-1)**n*factorial(n+1))','pscale(polys[n],factorial(n+1))'),
        source_case('Fourier-weight-exponents','FOURIER_MEASURE_NORMALIZATION','exponents=[2*F(7,6)-1,2*F(5,6)-1]','exponents=[2*F(5,6)-1,2*F(7,6)-1]'),
        source_case('Fourier-total-normalization','FOURIER_TOTAL_MASS','F(81,8)*hzero==2','F(81,9)*hzero==2'),
        source_case('finite-cubic-coefficient','FINITE_HAHN_CUBIC','mmul(mmul(mmul(J,comm),K),Km2),18','mmul(mmul(mmul(J,comm),K),Km2),17'),
        source_case('finite-boundary-retention','FINITE_BOUNDARY_DIAGONAL','defect[-1][-1]==3*n*(n-2)','defect[-1][-1]==0'),
        source_case('Jacobi-contiguous-coefficient','JACOBI_CONTIGUOUS','jacobi(n-1,a+1,b)),2*n+s)','jacobi(n-1,a+1,b)),2*n+s+1)'),
        source_case('shifted-gamma-factor','CONTIGUOUS_B_GAMMA','shifted=2*gamma_quotient','shifted=3*gamma_quotient'),
        source_case('gamma-amplitude-cancellation','GAMMA_FIRST_ORDER_CANCELLATION','target=spmul(a,spadd(s,one))','target=spmul(a,spadd(s,spscale(one,2)))'),
        source_case('overlap-factorization','OVERLAP_TRACE_FACTORIZATION','trace(mmul(A,B))==frobenius2','trace(A)*trace(B)==frobenius2'),
        source_case('mixed-Hessian-sign','MIXED_LOGDETERMINANT_HESSIAN','hessian==-4*trace','hessian==4*trace'),
        source_case('noncommuting-resolvent-order','NONCOMMUTING_RESOLVENT_FACTORIZATION','mmul(mmul(X,Ra),transpose(Y))','mmul(mmul(X,Ra),transpose(X))'),
        source_case('ordered-determinant-cross-term','ORDERED_DETERMINANT_FACTORIZATION','mmul(mmul(mmul(inverse(IA),A),B),inverse(IB))','mmul(mmul(mmul(inverse(IA),B),A),inverse(IB))'),
        source_case('tilted-projection-inverse','TILTED_ORTHOGONAL_PROJECTION','Q=mmul(mmul(mmul(mmul(E,S),Ti),ST),E)','Q=mmul(mmul(mmul(mmul(E,S),mpow(Ti,2)),ST),E)'),
        source_case('tilted-variance-subtraction','TILTED_VARIANCE_FACTORIZATION','hess=trace(mmul(Q,mpow(V,2)))-trace','hess=trace(mmul(Q,mpow(V,2)))+trace'),
        source_case('relative-skew-symmetry','RELATIVE_SKEW_TRACE_CANCELLATION','skew=[[F(i-j,17*d)','skew=[[F(i+j+1,17*d)'),
        source_case('relative-determinant-order-factor','RELATIVE_FINITE_DETERMINANT','mscale(mmul(R,error),delta)','mscale(mmul(R,error),2*delta)'),
        source_case('inverse-center-constant','INVERSE_CENTER_EXACT_CANCELLATION','spterm([-2,2,0,0,0],F(1,8))','spterm([-2,2,0,0,0],F(1,7))'),
        source_case('inverse-log-coordinate','INVERSE_CENTER_Y_SUBSTITUTION','spscale(spvar(6,2),F(1,2))','spscale(spvar(6,2),F(1,3))'),
    ]
    return out

def main():
    original=snapshot(ROOT); definitions=cases(); rows=[]; baseline=[]
    with tempfile.TemporaryDirectory(prefix='report124-checks-') as tmp:
        tmp=Path(tmp)
        for optimized in (False,True):
            root=tmp/('baseline-optimized' if optimized else 'baseline-normal'); shutil.copytree(ROOT,root)
            rc,result=run_copy(root,optimized)
            require(rc==0 and result.get('status')=='PASS','NEGATIVE_BASELINE_FAILED',result)
            baseline.append(result)
        require(baseline[0]==baseline[1],'NEGATIVE_OPTIMIZATION_CHANGED_RESULT')
        for index,(name,diagnostic,mutate,reseal) in enumerate(definitions):
            for optimized in (False,True):
                root=tmp/(str(index)+('-O' if optimized else '-normal')); shutil.copytree(ROOT,root)
                mutate(root)
                if reseal: seal(root)
                rc,result=run_copy(root,optimized)
                require(rc==1 and result.get('status')=='FAIL' and result.get('diagnostic')==diagnostic,'NEGATIVE_WRONG_FAILURE',{'name':name,'optimized':optimized,'expected':diagnostic,'exit':rc,'actual':result})
                rows.append({'mutation':name,'optimized':optimized,'diagnostic':diagnostic,'exit':rc,'bytes_unchanged_by_run':True})
    require(snapshot(ROOT)==original,'NEGATIVE_SOURCE_CHANGED')
    return {'status':'PASS','report':'report124','positive_baselines':2,'positive_results_identical':True,'mutation_definitions':len(definitions),'expected_failures':len(rows),'closed_directory_bytes_unchanged':True,'coverage':'Selected schema, provenance, integrity and mathematical paths; not exhaustive mutation coverage','cases':rows}

if __name__=='__main__':
    try: print(json.dumps(main(),sort_keys=True,indent=2))
    except Failure as ex:
        print(json.dumps({'status':'FAIL','diagnostic':ex.code,'detail':ex.detail},sort_keys=True)); sys.exit(1)
    except Exception as ex:
        print(json.dumps({'status':'ERROR','diagnostic':'UNEXPECTED_EXCEPTION','detail':type(ex).__name__+': '+str(ex)},sort_keys=True)); sys.exit(2)
