#!/usr/bin/env python3
"""Portable verifier for the exact K215 composed-selector research packet.

Default: authenticate the available manifest and two parent archives; extract
only three pinned inputs; reconstruct the four machine/source artifacts;
check all source and decoder contexts; rerun the independent blank-table
audit and local helper diamond; replay the delivered blank trace; check
the complete stored primitive-certificate inventory and raw-address/ordinal
interface; and replay both inherited finite logical-bridge checkers.

--runtime additionally derives every universal primitive case afresh and
compares the ordered case receipts and complete startup data by decompressed
content. This remains ordinary mathematical symbolic evidence, not a new
Lean/Rocq kernel endpoint. The inherited logical calibration is documented
in the report and retained parent archives; their entire historical suites
are not rerun here.

Python 3.10 or newer, standard library only. Assertions must remain enabled.
"""
from pathlib import Path, PurePosixPath
import argparse, gzip, hashlib, json, os, subprocess, sys, tempfile, zipfile

if not __debug__ or sys.flags.optimize:
    raise SystemExit('Verification requires assertions: remove -O and PYTHONOPTIMIZE.')

PARTIAL='K216_Partial_Selector_2026-10-20'
PERMUTED='K216_Permuted_Commands_2026-10-21'
ARCHIVE_PINS={
    PARTIAL+'.zip':'05c4e63b64e64426fe1c909c0cd2490146fe13805b51f5016b6ff9dd8748ebcc',
    PERMUTED+'.zip':'c9b9a3355316cf084c86a702cce092fe4ea16bf837e9b258cb1c2fd87ac5a4f3',
}
NATIVE_PIN='03739f080d023166773bc14e7e3a4d8157f81d44c28cd30fef46066b37cf3748'
DENSE_PIN='fd9de5a9702c6193350952ca85a43f65d288b20f234b7582549b6aaa7a5ce703'
SOURCE_PIN='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
PHY=(6,2,0,4,3,7,8,5,1)

def require(ok,message):
    if not ok:raise ValueError(message)
def load(path):return json.loads(Path(path).read_text())
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()
def dump(path,value):Path(path).write_text(json.dumps(value,indent=2)+'\n')
def gunzip_json(path):
    with gzip.open(path,'rt',encoding='utf-8')as f:return json.load(f)
def gzip_content_equal(left,right):
    with gzip.open(left,'rb')as a,gzip.open(right,'rb')as b:
        while True:
            x,y=a.read(1024*1024),b.read(1024*1024)
            if x!=y:return False
            if not x:return True

def check_manifest(root):
    path=root/'manifest.json'
    if not path.exists():return {'present':False,'verified_files':0}
    obj=load(path);entries=obj.get('files',obj)if isinstance(obj,dict)else obj
    if isinstance(entries,dict):
        records=[{'path':p,'sha256':v}if isinstance(v,str)else {'path':p,**v}for p,v in entries.items()]
    else:
        require(isinstance(entries,list),'Unsupported manifest shape')
        records=entries
    require(records,'Manifest is empty');seen=set()
    for item in records:
        require(isinstance(item,dict)and'path'in item and'sha256'in item,'Malformed manifest record')
        name=item['path'];p=PurePosixPath(name)
        require(isinstance(name,str)and not p.is_absolute()and'..'not in p.parts and str(p)==name,'Unsafe manifest path')
        require(name not in seen and name!='manifest.json','Duplicate/self manifest entry');seen.add(name)
        target=root.joinpath(*p.parts)
        require(target.is_file(),f'Missing manifest member: {name}')
        require(sha(target)==item['sha256'],f'Manifest SHA-256 mismatch: {name}')
        expected_size=item.get('size_bytes',item.get('size'))
        if expected_size is not None:require(target.stat().st_size==expected_size,f'Manifest size mismatch: {name}')
    return {'present':True,'verified_files':len(records),'scope':'Every listed member hash and any listed size were checked.'}

def run_script(root,work,label,script,*args,subdir='code'):
    script=root/subdir/script
    require(script.is_file(),f'Missing verifier: {script.name}')
    print('RUN',label,flush=True)
    command=[sys.executable,'-B',str(script),*[str(x)for x in args]]
    result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,check=False)
    (work/(label+'.log')).write_text(result.stdout)
    if result.returncode:
        print(result.stdout,file=sys.stderr)
        raise RuntimeError(f'{label} failed with exit code {result.returncode}')
    print('PASS',label,flush=True)
    return result.stdout

def extract_inputs(root,work):
    selected=((PARTIAL,'machine/k216.native.tm','parent.native.tm'),
              (PARTIAL,'source/sites216.json','parent_sites.json'),
              (PERMUTED,'machine/sites216.json','reference_sites.json'))
    for name,pin in ARCHIVE_PINS.items():
        p=root/'parent'/name
        require(p.is_file(),f'Missing parent archive: {name}')
        require(sha(p)==pin,f'Parent archive hash mismatch: {name}')
    inputs=work/'inputs';inputs.mkdir()
    for stem,relative,filename in selected:
        archive=root/'parent'/(stem+'.zip');member=stem+'/'+relative
        with zipfile.ZipFile(archive)as z:
            infos=[i for i in z.infolist()if i.filename==member]
            require(len(infos)==1 and not infos[0].is_dir(),f'Parent member not unique: {member}')
            require(infos[0].file_size<5*1024*1024,'Unexpectedly large pinned parent input')
            (inputs/filename).write_bytes(z.read(infos[0]))
    return inputs

def read_table(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b)not in table and b in(0,1)and w in(0,1)and d in('L','R'),'Malformed literal table')
        table[q,b]=(w,1 if d=='R'else-1,z)
    return table

def replay_stored_startup(root,T):
    st=gunzip_json(root/'evidence/startup.json.gz')
    require(st.get('status')=='SAFE_SOURCE_ROOT'and st.get('steps')==95726,'Wrong stored startup declaration')
    trace=st['trace'];require(len(trace)==95726,'Stored startup has wrong length')
    q=h=0;ones=set();lo=hi=0
    for tick,entry in enumerate(trace):
        b=int(h in ones);require((q,b)in T,f'Premature halt at startup step {tick}')
        w,d,z=T[q,b]
        require(entry==[q,h,b,w,d,z],f'Stored startup transition mismatch at {tick}')
        if w:ones.add(h)
        else:ones.discard(h)
        q=z;h+=d;lo=min(lo,h);hi=max(hi,h)
    physical=[0]*9;physical[PHY[0]]=4;expected={-9,57};p=58
    for value in physical+[1]*40:
        p+=1;expected.update(range(p,p+value+1));p+=value+1
    require((q,h,lo,hi)==(84,-8,-18,199),'Stored startup has wrong control/head range')
    require(ones==expected and len(ones)==95,'Stored startup has wrong complete tape')
    require(st['one_cells']==sorted(expected)and st['registers']==[4,0,0,0,0,0,0,0,0],'Stored seed metadata mismatch')
    require(st['spares']==[1]*40 and st['gap']==1 and st['header']==57,'Stored seed frame mismatch')
    summary=load(root/'evidence/startup_summary.json')
    require(summary.get('table_sha256')==sha(root/'machine/k215.native.tm'),'Stored seed table binding')
    require({k:v for k,v in summary.items()if k!='table_sha256'}=={k:v for k,v in st.items()if k!='trace'},'Stored startup summary disagrees with trace record')
    return {'steps':95726,'complete_tape_checked':True,'one_cells':95,'registers':[4,0,0,0,0,0,0,0,0]}

def stored_inventory(root,T,sites):
    report=load(root/'evidence/runtime.json');cases_path=root/'evidence/runtime_cases.json.gz'
    require(report.get('status')=='UNIVERSAL_MATHEMATICAL_PASS','Stored runtime is not a completed proof receipt')
    bindings={'table_sha256':root/'machine/k215.native.tm','source_sha256':root/'source/sites215.json',
              'checker_sha256':root/'code/runtime/symbolic_runtime.py','helper_sha256':root/'code/runtime/independent_runtime.py',
              'wrapper_sha256':root/'code/validate_runtime.py','case_receipts_sha256':cases_path}
    for field,path in bindings.items():require(report.get(field)==sha(path),f'Stored runtime binding mismatch: {field}')
    mp={int(k):int(v)for k,v in load(root/'code/inputs/legacy_mapping.json').items()}
    states={q for q,b in T}
    for q in states|{254}:
        if q not in mp:mp[q]=q+1000
    require(len({mp[q]for q in states|{254}})==len(states)+1,'Noninjective runtime state map')
    renamed={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}
    expected=[(i,positive)for i,site in enumerate(sites)for positive in((False,True)if site[1]=='CD'else(False,))]
    cases=gunzip_json(cases_path)
    require(len(cases)==len(expected)==6176,'Stored case count mismatch')
    covered=set();steps=0;minimum=None
    for record,(i,positive)in zip(cases,expected):
        require(record['site_index']==i and type(record['positive'])is bool and record['positive']==positive,'Stored guarded-case order mismatch')
        duration=record['duration'];motion=record['motion']
        require(len(duration)==13 and all(type(x)is int and x>=0 for x in duration)and duration[0]>0,'Nonpositive/invalid affine case duration')
        require(len(motion)==13 and all(type(x)is int for x in motion),'Invalid affine motion vector')
        rows=[tuple(x)for x in record['rows']]
        require(rows==sorted(set(rows))and all(x in renamed for x in rows),'Invalid case transition inventory')
        require(type(record['symbolic_steps'])is int and record['symbolic_steps']>0,'Invalid symbolic-step count')
        require(sum(record['kinds'].values())==record['symbolic_steps'],'Symbolic-rule inventory mismatch')
        covered.update(rows);steps+=record['symbolic_steps'];minimum=duration[0]if minimum is None else min(minimum,duration[0])
    for block in report['blocks']:
        for event in block['trace']:
            if event[0]in('literal','unary'):
                q,b,w,d,z=event[1]
                require(renamed.get((q,b))==(w,d,z),'Stored one-block proof uses a different literal transition')
                covered.add((q,b))
    require(covered==set(renamed),'Stored inventory does not cover every transition')
    require((steps,minimum)==(1698790,6),'Unexpected stored proof totals')
    checks={'working_states':215,'transition_rows':430,'primitive_occurrences':4751,'expected_cases':6176,'proved_cases':6176,
            'symbolic_steps':steps,'minimum_duration_constant':minimum,'all_transition_rows_covered':True}
    for key,value in checks.items():require(report.get(key)==value,f'Stored runtime summary mismatch: {key}')
    return {**checks,'scope':'Stored certificate identities, complete ordered guard inventory, positive affine clocks and literal row coverage; not a fresh primitive proof derivation.'}

def verify(root,work,fresh_runtime):
    manifest=check_manifest(root)
    for relative,pin in(('machine/k215.native.tm',NATIVE_PIN),('machine/k215.tm',DENSE_PIN),('source/sites215.json',SOURCE_PIN)):
        require(sha(root/relative)==pin,f'Wrong final artifact: {relative}')
    inputs=extract_inputs(root,work);built=work/'reconstructed'
    run_script(root,work,'reconstruct','reconstruct215.py',
        '--parent-table',inputs/'parent.native.tm','--parent-source',inputs/'parent_sites.json',
        '--reference-sites',inputs/'reference_sites.json','--output',built)
    products={'k215.native.tm':'machine/k215.native.tm','k215.tm':'machine/k215.tm',
              'sites215.json':'source/sites215.json','canonicalization.json':'machine/canonicalization.json'}
    for made,delivered in products.items():require((built/made).read_bytes()==(root/delivered).read_bytes(),f'Reconstructed artifact differs: {made}')
    require(load(built/'reconstruction.json')==load(root/'evidence/reconstruction.json'),'Construction receipt mismatch')
    run_script(root,work,'decoder','audit_decoder215.py',
        '--parent-table',inputs/'parent.native.tm','--parent-source',inputs/'parent_sites.json',
        '--candidate-table',root/'machine/k215.native.tm','--candidate-source',root/'source/sites215.json',
        '--output',work/'decoder.json')
    run_script(root,work,'source','source_compare.py',inputs/'reference_sites.json',root/'source/sites215.json',work/'source.json')
    require(load(work/'source.json')==load(root/'evidence/source_bisimulation.json'),'Independent source-bisimulation receipt mismatch')
    run_script(root,work,'blank','audit_table_and_blank.py','--native',root/'machine/k215.native.tm',
        '--canonical',root/'machine/k215.tm','--mapping',root/'machine/canonicalization.json','--output',work/'blank.json')
    run_script(root,work,'row81','check_row81_diamond.py',inputs/'parent.native.tm','--output',work/'row81.json')
    T=read_table(root/'machine/k215.native.tm');sites=load(root/'source/sites215.json')
    startup=replay_stored_startup(root,T);inventory=stored_inventory(root,T,sites)
    run_script(root,work,'runtime_interface','review_runtime215.py',root,'--output',work/'runtime_review.json')
    require(load(work/'runtime_review.json')==load(root/'evidence/runtime_review.json'),'Independent runtime-interface receipt mismatch')
    logical_receipts=load(root/'theory/fresh_replay.json')['receipts']
    for label,script in(('logical_interned','check_classical_compact.py'),('logical_tuples','audit_classical_independent.py')):
        result=json.loads(run_script(root,work,label,script,root/'theory/dominated_rho8_full_certificate.json',subdir='theory'))
        require(result.get('verified')is True and result.get('proof_nodes')==3728 and result.get('shared_terms')==5160,'Incomplete finite logical-bridge replay')
        require(result==logical_receipts[script],f'Finite logical-bridge receipt differs: {script}')
    if fresh_runtime:
        out=work/'runtime'
        run_script(root,work,'runtime','validate_runtime.py',root/'machine/k215.native.tm',root/'source/sites215.json',out)
        for name in('runtime_cases.json.gz','startup.json.gz'):
            require(gzip_content_equal(out/name,root/'evidence'/name),f'Fresh decompressed receipt differs: {name}')
        require(load(out/'startup_summary.json')==load(root/'evidence/startup_summary.json'),'Fresh startup summary differs')
        delivered=load(root/'evidence/runtime.json');fresh=load(out/'runtime.json')
        ignored={'seconds','case_receipts_sha256'}
        require({k:v for k,v in fresh.items()if k not in ignored}=={k:v for k,v in delivered.items()if k not in ignored},'Fresh runtime proof summary differs')
    result={'status':'K215_FULL_FRESH_REPLAY_PASS'if fresh_runtime else'K215_DEFAULT_VERIFICATION_PASS',
        'working_states':215,'rows':430,'native_sha256':NATIVE_PIN,'canonical_sha256':DENSE_PIN,'source_sha256':SOURCE_PIN,
        'manifest':manifest,'parent_archive_hashes_checked':2,'parent_members_extracted':3,'constructed_outputs_compared':4,
        'all_compound_prefixes_checked':4750,'complete_source_bisimulation_checked':True,'independent_blank_audit':True,
        'parent_row81_diamond_checked':True,'stored_startup_replayed':startup,'stored_runtime_inventory':inventory,
        'all_6175_raw_address_ordinal_successors_checked':True,'finite_logical_bridge_rederived_by_two_checkers':True,
        'unbounded_runtime_rederived':fresh_runtime,'fresh_case_receipts_compared_by_decompressed_content':fresh_runtime,
        'scope':'Exact finite construction/source/blank/interface checks, authenticated stored symbolic inventory, and two replays of the finite dominated-rho8 bridge. --runtime additionally rederives the arbitrary-natural primitive contracts. The foundational native-calculus/ZFC calibration is retained and cited, not re-proved by this script; no new proof-assistant kernel endpoint is claimed.'}
    dump(work/'verification.json',result);print(json.dumps(result,indent=2),flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime',action='store_true',help='Freshly derive all 6,176 arbitrary-natural primitive cases (about a few minutes).')
    ap.add_argument('--work',type=Path,help='New output directory outside the packet; retain all verification logs and receipts here.')
    ap.add_argument('--package-root',type=Path,default=Path(__file__).resolve().parent,help='Packet root; defaults to the directory containing this script.')
    a=ap.parse_args();root=a.package_root.resolve();require(root.is_dir(),'Packet root does not exist')
    if a.work:
        work=a.work.resolve();require(work!=root and root not in work.parents,'Work directory must be outside the packet')
        require(not work.exists(),'Work directory already exists; choose a new directory')
        work.mkdir(parents=True);verify(root,work,a.runtime)
    else:
        with tempfile.TemporaryDirectory(prefix='k215-verify-')as directory:verify(root,Path(directory),a.runtime)

if __name__=='__main__':main()
