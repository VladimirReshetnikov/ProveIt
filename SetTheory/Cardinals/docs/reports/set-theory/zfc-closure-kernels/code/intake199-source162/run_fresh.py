#!/usr/bin/env python3
"""Run seven source-reviewed Source162 leaves on fresh copies; stdlib only.

Supply the exact extracted packet and three existing selected parent files.
No archive-level wrappers or manifests are read. Assertions stay enabled.
"""
import argparse, datetime, gzip, hashlib, json, os, signal, shutil, subprocess, sys, time
from pathlib import Path

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):
    tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(x,indent=2)+'\n');tmp.replace(p)
def load(p): return json.loads(p.read_text())
def gload(p):
    with gzip.open(p,'rt') as f:return json.load(f)
def need(ok,msg):
    if not ok:raise ValueError(msg)
def relsafe(s):
    p=Path(s);need(not p.is_absolute() and '..' not in p.parts,'Unsafe selected path');return p

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',type=Path,required=True)
    ap.add_argument('--parent-table',type=Path,required=True)
    ap.add_argument('--parent-source',type=Path,required=True)
    ap.add_argument('--reference-source',type=Path,required=True)
    ap.add_argument('--inputs',type=Path,default=Path(__file__).with_name('fresh-inputs.json'))
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();need(__debug__ and not sys.flags.optimize,'Assertions required')
    spec=load(a.inputs);need(spec['schema']=='source162-seven-selected-leaves-v1','Wrong input schema')
    out=a.out.resolve();need(not out.exists(),'Output already exists; preserve earlier attempts')
    originals={}
    for name,pin in spec['packet_inputs'].items():
        p=a.packet.resolve()/relsafe(name);need(p.is_file() and not p.is_symlink(),'Missing/nonregular input '+name)
        need(sha(p)==pin,'Changed reviewed input '+name);originals['packet/'+name]=p
    for name,row in spec['parents'].items():
        p=getattr(a,name).resolve();need(p.is_file() and sha(p)==row['sha256'],'Changed selected parent '+name)
        originals['parents/'+name+'/'+row['name']]=p
    before={k:sha(p) for k,p in originals.items()}
    out.mkdir(parents=True);copies={}
    for name,p in originals.items():
        q=out/'inputs'/name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q);copies[name]=q
    (out/'logs').mkdir();(out/'results').mkdir()
    fields={'packet':str(out/'inputs/packet'),'out':str(out/'results')}
    for name,row in spec['parents'].items():fields[name]=str(out/'inputs/parents'/name/row['name'])
    rec={'status':'RUNNING_SELECTED_SOURCE162_LEAVES','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'runner_sha256':sha(Path(__file__)),'inputs_spec_sha256':sha(a.inputs),'python':sys.version,'assertions_enabled':True,
         'invocation':sys.argv,'scope':spec['excluded'],'original_inputs':{k:str(p) for k,p in originals.items()},
         'before':before,'jobs':[]}
    dump(out/'actual.json',rec)
    env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONUNBUFFERED']='1'
    try:
        for job in spec['jobs']:
            argv=[str(x).format(**fields) for x in job['argv']];argv[0]=sys.executable
            stdout=out/'logs'/(job['name']+'.stdout');stderr=out/'logs'/(job['name']+'.stderr')
            print('START',job['name'],'cap',job['timeout_seconds'],flush=True);start=time.monotonic();timed=False
            with stdout.open('wb') as so,stderr.open('wb') as se:
                proc=subprocess.Popen(argv,cwd=fields['packet'],env=env,stdout=so,stderr=se,start_new_session=True)
                try:rc=proc.wait(timeout=job['timeout_seconds'])
                except subprocess.TimeoutExpired:
                    timed=True;os.killpg(proc.pid,signal.SIGKILL);rc=proc.wait()
            row={'name':job['name'],'argv':argv,'cwd':fields['packet'],'timeout_seconds':job['timeout_seconds'],
                 'returncode':rc,'timed_out':timed,'seconds':time.monotonic()-start,
                 'stdout':{'path':str(stdout.relative_to(out)),'sha256':sha(stdout)},
                 'stderr':{'path':str(stderr.relative_to(out)),'sha256':sha(stderr)}}
            rec['jobs'].append(row);dump(out/'actual.json',rec)
            print('FINISH',job['name'],rc,round(row['seconds'],3),flush=True)
            need(rc==0 and not timed,'Selected job failed: '+job['name'])
            need(all(sha(p)==before[k] for k,p in copies.items()),'Copied input changed')
            need(all(sha(p)==before[k] for k,p in originals.items()),'Original input changed')
        p=out/'inputs/packet';r=out/'results'
        expected={'rebuild/reconstruction.json':'EXACT_K215_CONSTRUCTION_AND_SOURCE_BISIMULATION_PASS',
                  'decoder.json':'EXACT_K215_ALL_PREFIX_BINDINGS_PASS','blank.json':'INDEPENDENT_K215_TABLE_AND_BLANK_PASS',
                  'runtime/runtime.json':'UNIVERSAL_MATHEMATICAL_PASS','saved-interface.json':'INDEPENDENT_INTERFACE_AND_RECEIPT_AUDIT_PASS'}
        for name,status in expected.items():need(load(r/name)['status']==status,'Wrong status '+name)
        pairs=[('rebuild/k215.native.tm','machine/k215.native.tm'),('rebuild/k215.tm','machine/k215.tm'),
               ('rebuild/sites215.json','source/sites215.json'),('rebuild/canonicalization.json','machine/canonicalization.json'),
               ('runtime/runtime_cases.json.gz','evidence/runtime_cases.json.gz'),('runtime/startup.json.gz','evidence/startup.json.gz')]
        matches=[]
        for fresh,saved in pairs:
            need((r/fresh).read_bytes()==(p/saved).read_bytes(),'Fresh/saved bytes differ: '+fresh)
            matches.append({'fresh':fresh,'saved':saved,'sha256':sha(r/fresh)})
        fresh=load(r/'runtime/runtime.json');saved=load(p/'evidence/runtime.json')
        need({k:v for k,v in fresh.items() if k!='seconds'}=={k:v for k,v in saved.items() if k!='seconds'},'Runtime report differs beyond duration')
        control=load(out/'logs/rejected_CB1.stdout');need(control['status']=='CONCRETE_REJECTED_SHORTCUT_COUNTEREXAMPLE' and control['corrected_primitive_status']=='PASS_THIS_CONCRETE_FRAME','Missing old-failure/new-pass control')
        rec.update(status='SEVEN_SELECTED_SOURCE162_LEAVES_PASS',fresh_saved_byte_matches=matches,
                   runtime_report_matches_except_elapsed_seconds=True,
                   fresh_runtime={k:fresh[k] for k in ['working_states','transition_rows','primitive_occurrences','proved_cases','symbolic_steps','minimum_duration_constant','all_transition_rows_covered','seconds']},
                   startup={k:gload(r/'runtime/startup.json.gz')[k] for k in ['steps','state','head','header','gap','registers','spares','one_cells','head_range']})
    except BaseException as e:
        rec.update(status='FAIL_SELECTED_SOURCE162_LEAVES',error=type(e).__name__+': '+str(e));raise
    finally:
        rec['after']={k:sha(p) if p.is_file() else None for k,p in originals.items()}
        rec['copied_after']={k:sha(p) if p.is_file() else None for k,p in copies.items()}
        rec['inputs_unchanged']=rec['after']==before and rec['copied_after']==before
        rec['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        rec['outputs']={str(p.relative_to(out/'results')):{'sha256':sha(p),'size':p.stat().st_size} for p in sorted((out/'results').rglob('*')) if p.is_file()}
        dump(out/'actual.json',rec)
    print(rec['status'],sha(out/'actual.json'),flush=True)
if __name__=='__main__':main()
