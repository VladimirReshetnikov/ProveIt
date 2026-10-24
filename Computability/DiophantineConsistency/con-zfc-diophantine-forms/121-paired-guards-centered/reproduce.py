#!/usr/bin/env python3
"""Offline isolated normal/-O replay. No producer/source directory is mutated.

A manifest is an integrity inventory, not a signature or a mathematical proof.
Run only a release whose code/provenance you have reviewed and trust.
"""
from pathlib import Path
import argparse, copy, gzip, hashlib, json, os, platform, shutil, subprocess, sys, tempfile, time, zipfile
ROOT=Path(__file__).resolve().parent
EXCLUDED={'MANIFEST.json'}

def need(test,msg):
    if not test:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def ignored(rel):return rel.as_posix() in EXCLUDED or '__pycache__' in rel.parts or rel.suffix=='.pyc'
def inventory(root):
    answer={}
    for p in root.rglob('*'):
        need(not p.is_symlink(),'symlink is not a portable release file: '+str(p))
        if p.is_file() and not ignored(p.relative_to(root)):answer[p.relative_to(root).as_posix()]=p
    return answer

def verify_manifest(root):
    manifest=json.loads((root/'MANIFEST.json').read_text());listed={}
    for row in manifest['files']:
        rel=Path(row['path'])
        need(not rel.is_absolute() and '..' not in rel.parts,'unsafe manifest path')
        need(row['path'] not in listed,'duplicate manifest entry')
        listed[row['path']]=row
    actual=inventory(root)
    need(set(actual)==set(listed),'manifest inventory differs; missing='+str(sorted(set(listed)-set(actual)))+' extra='+str(sorted(set(actual)-set(listed))))
    for name,p in actual.items():
        raw=p.read_bytes();row=listed[name]
        need(len(raw)==row['bytes'] and sha(raw)==row['sha256'],'manifest mismatch: '+name)
    return {'status':'PASS','files':len(listed),'bytes':sum(r['bytes'] for r in listed.values()),'manifest_sha256':sha((root/'MANIFEST.json').read_bytes())}

def verify_prior(root):
    prior=root/'prior/ZFC_Diophantine_Coprime_Projection'
    rows=json.loads((prior/'MANIFEST.json').read_text())['files']
    for row in rows:
        p=prior/row['path'];raw=p.read_bytes()
        need(len(raw)==row['bytes'] and sha(raw)==row['sha256'],'immutable prior manifest '+row['path'])
    return {'status':'PASS','files':len(rows),'scope':'Whole inherited release bytes checked. Prior release programs and inherited formal projects are not executed by this round.'}


def verify_component_manifests(root):
    results={}
    for name,filename in [('integer','MANIFEST.json'),('lowdegree','MANIFEST.json'),('positive','MANIFEST.json'),('alternative','MANIFEST.sha256.json')]:
        data=json.loads((root/name/filename).read_text());rows=data.get('files',data)
        pairs=[(r['path'],r) for r in rows] if isinstance(rows,list) else rows.items()
        count=0
        for rel,record in pairs:
            expected=record if isinstance(record,str) else record.get('sha256')
            need(expected is not None,'unrecognized component manifest record')
            p=Path(rel);need(not p.is_absolute() and '..' not in p.parts,'unsafe component manifest path')
            raw=(root/name/p).read_bytes();need(sha(raw)==expected,'component manifest '+name+'/'+rel)
            if isinstance(record,dict) and 'bytes' in record:need(len(raw)==record['bytes'],'component size '+rel)
            count+=1
        results[name]={'status':'PASS','files':count}
    return results

def transport_crc(root,temp,archive=None):
    if archive:
        path=Path(archive).resolve();need(path.is_file(),'archive missing')
    else:
        path=temp/'roundtrip.zip'
        with zipfile.ZipFile(path,'w',zipfile.ZIP_DEFLATED) as z:
            for p in sorted(root.rglob('*')):
                if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':z.write(p,root.name+'/'+p.relative_to(root).as_posix())
    with zipfile.ZipFile(path) as z:
        need(z.testzip() is None,'ZIP CRC failure')
        names=z.namelist();need(len(names)==len(set(names)),'duplicate ZIP names')
        for n in names:need(not Path(n).is_absolute() and '..' not in Path(n).parts,'unsafe ZIP member')
        roots={n.split('/')[0] for n in names if '/' in n};need(len(roots)==1,'one ZIP root required')
        prefix=next(iter(roots))+'/'
        for row in json.loads((root/'MANIFEST.json').read_text())['files']:
            need(z.read(prefix+row['path'])==(root/row['path']).read_bytes(),'ZIP bytes differ '+row['path'])
        need(z.read(prefix+'MANIFEST.json')==(root/'MANIFEST.json').read_bytes(),'ZIP manifest differs')
        return {'status':'PASS','kind':'supplied_archive' if archive else 'fresh_local_roundtrip','members':len(names),'sha256':sha(path.read_bytes())}

def manifest_negative_controls(root):
    victim=root/'lowdegree/equation.json';original=victim.read_bytes();out=[]
    for name,change in [('one_byte_equation_corruption',lambda: victim.write_bytes(original+b' ')),('missing_equation',lambda: victim.unlink())]:
        change()
        try:verify_manifest(root)
        except (ValueError,FileNotFoundError):out.append({'control':name,'status':'REJECTED'})
        else:raise ValueError('manifest accepted '+name)
        finally:victim.write_bytes(original)
    victim=root/'positive/coefficients/K.bin.gz';original=victim.read_bytes();victim.write_bytes(original[:-1]+bytes([original[-1]^1]))
    try:verify_manifest(root)
    except ValueError:out.append({'control':'coefficient_payload_corruption','status':'REJECTED'})
    else:raise ValueError('manifest accepted coefficient corruption')
    finally:victim.write_bytes(original)
    return out

def crc_negative_control(temp):
    p=temp/'corrupt_crc.zip'
    with zipfile.ZipFile(p,'w',zipfile.ZIP_STORED) as z:z.writestr('control.txt',b'known CRC control payload')
    data=bytearray(p.read_bytes())
    with zipfile.ZipFile(p) as z:
        info=z.getinfo('control.txt');offset=info.header_offset+30+len(info.filename.encode())+len(info.extra)
    data[offset]^=1;p.write_bytes(data)
    with zipfile.ZipFile(p) as z:need(z.testzip()=='control.txt','ZIP CRC did not reject corruption')
    return {'control':'single_byte_stored_ZIP_payload_corruption','status':'REJECTED'}

INTEGER_NAMES=['optimized_guard_fused11_direct','optimized_guard_fused11_aux','optimized_fused11_integral','optimized_fused11_rational','pair_fused11_integral','pair_fused11_rational','pair_fused11_rational_strong','pair_fused11_rational_sharp']
POSITIVE_NAMES=['uncentered','upper','sharp','ordinary_uncentered','ordinary_upper','ordinary_sharp']
ALTERNATIVE_NAMES=['METRICS.json','equation.json','expanded_polynomial.json','factored_source.json','factorization_certificate.json','pair_certificate.json','paired_source.json','presemantic_certificate.json','projection_certificate.json','terminal_elimination_certificate.json']
GENERATED=([f'integer/{n}.json' for n in INTEGER_NAMES]+['integer/METRICS.json','integer/METRICS_OPTIMIZED.json','lowdegree/equation.json','lowdegree/specification.json','lowdegree/twelve/equation.json']+[f'positive/{n}.json' for n in POSITIVE_NAMES]+[f'alternative/{d}/{n}' for d in ['paired','squared_paired'] for n in ALTERNATIVE_NAMES])

def run_mode(tree,mode,logs):
    optimized=mode=='optimized';prefix=[sys.executable,'-B']+(['-O'] if optimized else [])
    commands=[];compared=[]
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0');env.pop('PYTHONPATH',None);env.pop('PYTHONOPTIMIZE',None)
    def run(args,stdout_reference=None):
        number=len(commands)+1;start=time.monotonic()
        p=subprocess.run(prefix+args,cwd=tree,env=env,capture_output=True,timeout=900)
        logfile=f'{mode}_{number:02d}.txt';(logs/logfile).write_bytes(p.stdout+b'\n--- STDERR ---\n'+p.stderr)
        row={'argv':prefix+args,'cwd':'<isolated release copy>','returncode':p.returncode,'seconds':round(time.monotonic()-start,3),'stdout_sha256':sha(p.stdout),'stderr_sha256':sha(p.stderr),'log':str(logs/logfile)}
        commands.append(row);print(mode+': '+' '.join(args)+' -> '+str(p.returncode),flush=True)
        need(p.returncode==0,'command failed: '+str(args)+'\n'+p.stderr.decode(errors='replace'))
        if stdout_reference:
            need(p.stdout==(ROOT/stdout_reference).read_bytes(),'stdout certificate differs: '+stdout_reference)
            compared.append(stdout_reference)
        return p.stdout
    for name in GENERATED:(tree/name).unlink()
    for args in [['integer/build_prior_optimized.py'],['integer/build.py'],['lowdegree/build.py'],['lowdegree/twelve/build.py'],['positive/build.py'],['alternative/build_pairguards.py','alternative/source','alternative/paired'],['alternative/build_pairguards.py','alternative/source','alternative/squared_paired','--squared-radius']]:run(args)
    for name in GENERATED:
        need((tree/name).read_bytes()==(ROOT/name).read_bytes(),'deterministic artifact differs: '+name);compared.append(name)
    run(['integer/check.py'])
    integer_receipt='integer/CHECK_OPTIMIZED.json' if optimized else 'integer/CHECK.json'
    need((tree/integer_receipt).read_bytes()==(ROOT/integer_receipt).read_bytes(),'integer certificate differs');compared.append(integer_receipt)
    for script,receipt in [('lowdegree/review/audit.py','lowdegree/review/CHECK.json'),('lowdegree/twelve/review/audit.py','lowdegree/twelve/review/CHECK.json'),('review/lowdegree/independent_audit.py','review/lowdegree/INDEPENDENT_CHECK.json')]:
        run([script]);need((tree/receipt).read_bytes()==(ROOT/receipt).read_bytes(),'audit certificate differs: '+receipt);compared.append(receipt)
    run(['positive/build.py','--check'])
    run(['positive/check.py'],'positive/CHECK_OPTIMIZED.json' if optimized else 'positive/CHECK.json')
    run(['positive/check_ordinary.py'],'positive/CHECK_ORDINARY_OPTIMIZED.json' if optimized else 'positive/CHECK_ORDINARY.json')
    run(['review/positive/independent_audit.py'],'review/positive/INDEPENDENT_CHECK_OPTIMIZED.json' if optimized else 'review/positive/INDEPENDENT_CHECK.json')
    run(['alternative/check_components.py'],'alternative/COMPONENT_CHECK_OPTIMIZED.json' if optimized else 'alternative/COMPONENT_CHECK.json')
    for variant in ['paired','squared_paired']:
        extra=['--squared-radius'] if variant=='squared_paired' else []
        run(['review/alternative/audit_paired_independent.py','--baseline','alternative/source','--candidate','alternative/'+variant,'--output','replay_generated/'+variant]+extra)
        run(['review/alternative/check_negative_controls.py','--baseline','alternative/source','--candidate','alternative/'+variant,'--output','replay_generated/'+variant+'/NEGATIVE_CONTROLS.json']+extra)
        reference='review/alternative/'+variant
        for filename in ['PRESEMANTIC_BOUNDS.json','NEGATIVE_CONTROLS.json']:
            need((tree/'replay_generated'/variant/filename).read_bytes()==(ROOT/reference/filename).read_bytes(),'independent certificate differs: '+reference+'/'+filename);compared.append(reference+'/'+filename)
        # Candidate path is intentionally machine-local metadata, not a proof term.
        generated=json.loads((tree/'replay_generated'/variant/'INDEPENDENT_REPLAY.json').read_text())
        archived=json.loads((ROOT/reference/'INDEPENDENT_REPLAY.json').read_text())
        generated.pop('candidate');archived.pop('candidate')
        need(generated==archived,'independent replay fields differ: '+variant)
    run(['review/integer/check_independent.py'])
    integer_review='review/integer/INDEPENDENT_CHECK_OPTIMIZED.json' if optimized else 'review/integer/INDEPENDENT_CHECK.json'
    need((tree/integer_review).read_bytes()==(ROOT/integer_review).read_bytes(),'independent integer certificate differs');compared.append(integer_review)
    run(['rebuild_coefficients.py'],'COEFFICIENT_CHECK.json')
    run(['report/qa/check_editorial_math.py'],'report/qa/editorial_math_check_optimized.json' if optimized else 'report/qa/editorial_math_check.json')
    # Every distributed coefficient payload and binding is unchanged, including
    # immutable dependencies. Audits above independently validate their meaning.
    coefficients=[]
    for p in ROOT.rglob('*'):
        if p.is_file() and ('coefficients' in p.parts or p.name.endswith('_certificate.json')):
            rel=p.relative_to(ROOT);need((tree/rel).read_bytes()==p.read_bytes(),'coefficient/certificate changed: '+str(rel));coefficients.append(rel.as_posix())
    verify_prior(tree)
    return {'status':'PASS','commands':commands,'deterministic_byte_comparisons':sorted(set(compared)),'preserved_coefficient_and_certificate_files':sorted(coefficients)}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--archive',type=Path,help='Also validate CRC and contents of the final distributed ZIP');ap.add_argument('--verify-only',action='store_true',help='Only static manifest, inherited inventory, and ZIP CRC');ap.add_argument('--receipt',type=Path,help='External JSON receipt path; default is a sibling replay-evidence directory');a=ap.parse_args()
    receipt=(a.receipt or ROOT.parent/(ROOT.name+'_replay')/'REPRODUCE_CHECK.json').resolve()
    need(not receipt.is_relative_to(ROOT),'receipt must be outside the immutable release')
    receipt.parent.mkdir(parents=True,exist_ok=True)
    if not a.verify_only:
        import sympy
    result={'schema':'isolated_release_replay_v1','status':'RUNNING','python':platform.python_version(),'sympy':sympy.__version__ if not a.verify_only else 'not imported for static verification','scope':'Finite algebra, deterministic transcription, source integrity and corruption controls; not a consistency proof or a fresh end-to-end Lean/C222/native compiler theorem.'}
    result['manifest']=verify_manifest(ROOT);result['prior']=verify_prior(ROOT);result['component_manifests']=verify_component_manifests(ROOT)
    with tempfile.TemporaryDirectory(prefix='conzfc-wave15-') as td:
        temp=Path(td);result['zip_crc']=transport_crc(ROOT,temp,a.archive);result['zip_corruption_control']=crc_negative_control(temp)
        if not a.verify_only:
            logs=receipt.parent/(receipt.stem+'_logs');logs.mkdir(exist_ok=True)
            for mode in ['normal','optimized']:
                tree=temp/mode
                def omit(directory,names):
                    return [n for n in names if n=='__pycache__' or n.endswith('.pyc')]
                shutil.copytree(ROOT,tree,ignore=omit)
                verify_manifest(tree)
                if mode=='normal':result['manifest_corruption_controls']=manifest_negative_controls(tree)
                result[mode]=run_mode(tree,mode,logs)
    result['manifest_after']=verify_manifest(ROOT);result['status']='PASS'
    receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result if a.verify_only else {'status':'PASS','receipt':str(receipt),'generated_files_per_mode':len(GENERATED),'commands_per_mode':len(result['normal']['commands'])},indent=2))
if __name__=='__main__':main()
