#!/usr/bin/env python3
"""Check frozen artifacts first, then replay only this release's own programs.

This is an exact finite reproducibility audit, not a formal proof of the
universal compiler, its logical endpoint, or either consistency assertion.
"""
from pathlib import Path
import argparse
from collections import Counter
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
from instance_binding import ALIASES, TUPLE_ID, TUPLE_SHA256, binding

ROOT = Path(__file__).resolve().parent
PIN = 'f0ae4e0991ca44a7bb4e5671d42e33d775e48035'
TM_SHA = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
TRANSITION_SHA = '880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755'
# File, independent variable count, gate count (None for sparse systems), degree.
EXPECTED = [
 ('amalgamation/main_root12_product.json',12,123,1145),
 ('amalgamation/main_root12_system.json',12,119,1136),
 ('amalgamation/main_root12_sos.json',12,126,2272),
 ('arithmetic/polynomial13_84_smallweight.json',13,84,515),
 ('arithmetic/system13_78_smallweight.json',13,78,488),
 ('arithmetic/sos13_89_smallweight.json',13,89,976),
 ('arithmetic/integer27_product136_smallweight.json',27,136,1004),
 ('arithmetic/integer27_system130_smallweight.json',27,130,952),
 ('arithmetic/integer27_sos141_smallweight.json',27,141,1904),
 ('arithmetic/integer27_product136.json',27,136,1116),
 ('arithmetic/integer27_system130.json',27,130,1064),
 ('arithmetic/integer27_sos141.json',27,141,2128),
 ('domains/integer54_quartic.json',54,None,4),
 ('domains/integer46_octic.json',46,None,8),
 ('domains/integer45_degree6.json',45,None,6),
 ('domains/integer39_degree8.json',39,None,8),
 ('domains/integer37_degree10.json',37,None,10),
 ('domains/integer35_degree12.json',35,None,12),
 ('domains/integer34_degree16.json',34,None,16),
]
REPLAYS = [
 ('amalgamation/build_root12.py', [], ['amalgamation/main_root12_product.json','amalgamation/main_root12_system.json','amalgamation/main_root12_sos.json','amalgamation/ROOT12_CHECKS.json']),
 ('arithmetic/build_integer27.py', [], ['arithmetic/integer27_product136.json','arithmetic/integer27_system130.json','arithmetic/integer27_sos141.json','arithmetic/integer27_verification.json']),
 ('arithmetic/build_smallweight.py', [], ['arithmetic/polynomial13_84_smallweight.json','arithmetic/system13_78_smallweight.json','arithmetic/sos13_89_smallweight.json','arithmetic/integer27_product136_smallweight.json','arithmetic/integer27_system130_smallweight.json','arithmetic/integer27_sos141_smallweight.json','arithmetic/smallweight_verification.json']),
 ('domains/build_domains.py', [], ['domains/integer54_quartic.json','domains/integer46_octic.json','domains/DOMAIN_CHECKS.json']),
 ('domains/build_tradeoffs.py', [], ['domains/integer45_degree6.json','domains/integer39_degree8.json','domains/integer37_degree10.json','domains/integer35_degree12.json','domains/integer34_degree16.json','domains/TRADEOFF_CHECKS.json']),
 ('review/check_root12_independent.py', [], ['review/ROOT12_INDEPENDENT_CHECKS.json']),
 ('review/check_smallweight_independent.py', [], ['review/SMALLWEIGHT_INDEPENDENT_CHECKS.json']),
 ('review/check_low_degree_independent.py', [], ['review/LOW_DEGREE_INDEPENDENT_CHECKS.json']),
 ('coefficients/load_coefficients.py', ['--rebuild'], ['coefficients/COEFFICIENTS.json','coefficients/tiles4094.json','coefficients/verification.json','coefficients/independent_count.json','coefficients/independent_audit.json','coefficients/expanded/MANIFEST.json','coefficients/expanded/beta.bin','coefficients/expanded/K.bin','coefficients/expanded/MC.bin','coefficients/expanded/MF_source.bin']),
]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while block:=f.read(1024*1024):h.update(block)
    return h.hexdigest()

def read(path):
    return json.loads(path.read_text())

def transitions(root):
    tm=root/'coefficients/sources/k215.tm'
    source=root/'coefficients/sources/k215_transitions.json'
    require(digest(tm)==TM_SHA,'literal k215.tm does not match its pinned hash')
    require(digest(source)==TRANSITION_SHA,'transition export does not match its pinned hash')
    rows=[]
    for raw in tm.read_text().splitlines():
        line=raw.strip()
        if not line or line.startswith('#'):continue
        q,b,w,m,nq=line.split()
        require(m in ['L','R'],'unexpected movement in original table')
        rows.append([int(q),int(b),int(w),{'L':-1,'R':1}[m],int(nq)])
    exported=read(source)
    require(rows==exported['transitions'],'430 exported transitions differ from literal table')
    require(len(rows)==430 and len({(r[0],r[1]) for r in rows})==430,'transition count/uniqueness')
    require({(r[0],r[1]) for r in rows}=={(q,b) for q in range(215) for b in (0,1)},'working-state domain')
    require(all(r[2] in (0,1) and 0<=r[4]<=215 for r in rows),'transition codomain')
    require(exported['source_sha256']['tm']==TM_SHA,'table provenance mismatch')
    return {'original_transitions':430,'literal_table_sha256':TM_SHA,'export_sha256':TRANSITION_SHA,'exact_ordered_match':True,'halt_padding':'Only the compiler adds two stationary identity transitions after the original machine halts.'}

def coefficients(root):
    spec=read(root/'coefficients/COEFFICIENTS.json')
    manifest=read(root/'coefficients/expanded/MANIFEST.json')
    require(spec['tuple_id']==TUPLE_ID and spec['tuple_sha256']==TUPLE_SHA256,'wrong selected tuple')
    ports=['beta','K','MC','MF_source']
    require(spec['polynomial_ports']==ports,'coefficient order mismatch')
    require(spec['scalars']['d']==5**11 and spec['scalars']['k']==4094,'coefficient scalar mismatch')
    total=0
    for port in ports:
        m=spec['numeric_coefficients'][port];p=root/'coefficients'/m['file']
        require(p.stat().st_size==m['size_bytes'],'coefficient size: '+port)
        require(digest(p)==m['sha256']==manifest['files'][port]['sha256'],'coefficient hash: '+port)
        raw=p.read_bytes();value=int.from_bytes(raw,'big')
        require(raw[0]!=0 and value.bit_length()==m['bit_length'],'minimal-width encoding: '+port)
        require(value.bit_count()==m['bit_population'],'coefficient population: '+port)
        total+=len(raw)
    require(hashlib.sha256(''.join(spec['numeric_coefficients'][n]['sha256'] for n in ports).encode('ascii')).hexdigest()==TUPLE_SHA256,'tuple digest definition')
    require(total==25421252==spec['numeric_total_bytes'],'numeric total bytes')
    require(digest(root/'coefficients/tiles4094.json')==spec['tiles_sha256'],'tile alphabet hash')
    require(len(read(root/'coefficients/tiles4094.json'))==4094,'tile alphabet length')
    require(read(root/'coefficients/independent_count.json')['total']==4094,'independent tile count')
    require(manifest['native_mask_population_sum']==5**11 and manifest['MC_mod4']==2 and manifest['native_MF_mod8']==4 and manifest['two_DC_minus_DR_mod5']==1,'native coefficient invariants')
    return {'tuple_id':TUPLE_ID,'tuple_sha256':TUPLE_SHA256,'complete_numeric_ports':ports,'numeric_total_bytes':total,'bit_population_checks':True,'tile_count':4094}

def packets(root):
    found=[]
    for folder in ['amalgamation','arithmetic','domains']:
        for p in (root/folder).glob('*.json'):
            data=read(p)
            if isinstance(data,dict) and ('source' in data or 'residuals' in data):found.append(str(p.relative_to(root)))
    require(set(found)=={r[0] for r in EXPECTED},'missing or unexpected main polynomial packet')
    result=[]
    for name,n,ops,degree in EXPECTED:
        p=read(root/name);vs=p.get('witnesses',p.get('variables'))
        require(len(vs)==len(set(vs))==n,'variable count: '+name)
        ports=p.get('fixed_numerals',p.get('fixed_integer_coefficients'))
        require(p['coefficient_binding']==binding(ports),'selected binding mismatch: '+name)
        require('historical_source_provenance' in p,'missing separated provenance: '+name)
        measured=p.get('exact_degree',p.get('exact_total_degree',p.get('exact_maximum_degree',max(p.get('residual_exact_degrees',[0])))))
        require(measured==degree,'advertised degree mismatch: '+name)
        record={'file':name,'variables':n,'degree':degree,'complete_binding':True}
        if ops is not None:
            src=p['source'];known=set(vs+ports)
            for register,op,a,b in src:
                require(register not in known and op in ['+','-','*'],'invalid register or operation: '+name)
                require(all(type(v) is int or v in known for v in (a,b)),'unbound circuit operand: '+name)
                known.add(register)
            outputs=[p['output']] if 'output' in p else [v for pair in p['comparisons'] for v in pair]
            needed={v for v in outputs if type(v) is str}
            for register,op,a,b in reversed(src):
                require(register in needed,'dead circuit gate: '+name)
                needed.update(v for v in (a,b) if type(v) is str)
            require(set(vs+ports)<=needed,'unused circuit port: '+name)
            counts=Counter(row[1] for row in src)
            require(len(src)==ops==p['ledger']['operations'],'operation count: '+name)
            require(counts['*']==p['ledger']['multiplications'] and counts['+']+counts['-']==p['ledger']['additions_subtractions'],'operation ledger: '+name)
            if 'source_sha256' in p:require(hashlib.sha256(json.dumps(src,separators=(',',':')).encode()).hexdigest()==p['source_sha256'],'source hash: '+name)
            record.update(operations=ops,multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],all_gates_and_ports_live=True)
        else:
            require(len(p['residuals'])==p.get('equation_count',p.get('number_of_equations')),'residual count: '+name)
            if 'parent_file' in p:require(digest(root/'domains'/p['parent_file'])==p['parent_sha256'],'parent data hash: '+name)
            record['squared_residuals']=len(p['residuals'])
        result.append(record)
    instance=read(root/'INSTANCE.json')
    require(instance['coefficient_tuple_id']==TUPLE_ID and instance['coefficient_tuple_sha256']==TUPLE_SHA256,'INSTANCE coefficient choice')
    require(instance['aliases']==ALIASES,'INSTANCE aliases')
    require(instance['main_artifacts']==[r[0] for r in EXPECTED],'INSTANCE artifact inventory')
    return result

def run(root,script,args):
    # Whitelist new code only. Nothing below a sources/ or dependencies/ path runs.
    permitted={r[0] for r in REPLAYS}|{'coefficients/audit_compact.py'}
    require(script in permitted and '/sources/' not in script and '/dependencies/' not in script,'refusing an unapproved replay target')
    print('Replay: '+script+' '+ ' '.join(args),flush=True)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    process=subprocess.run([sys.executable,str(root/script),*args],cwd=root,env=env,text=True,capture_output=True)
    require(process.returncode==0,'Replay failed: '+script+'\n'+process.stdout+'\n'+process.stderr)
    return {'command':['python',script,*args],'exit_code':process.returncode,'stdout_sha256':hashlib.sha256(process.stdout.encode()).hexdigest()}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick',action='store_true',help='Check frozen artifacts only; writes VERIFICATION.quick.json instead.')
    args=parser.parse_args()
    output=ROOT/('VERIFICATION.quick.json' if args.quick else 'VERIFICATION.json')
    receipt={'status':'RUNNING','mode':'shipped artifacts only' if args.quick else 'shipped-artifact preflight then temporary-copy full replay','repository_source_pin':PIN,
             'boundary':'Exact finite data, formula, count, coefficient and reproducibility checks. Ordinary mathematical proofs and inherited compiler/endpoint theorems are not kernel checked here. No ZFC consistency proof, accepting K215 run, or optimality claim.'}
    try:
        require(not sys.flags.optimize,'Run without -O: some component diagnostics use assertions.')
        receipt['coefficient_checks']=coefficients(ROOT)
        receipt['literal_transition_check']=transitions(ROOT)
        receipt['shipped_packets']=packets(ROOT)
        print('PASS: shipped numeric coefficients, 430 literal transitions and all 19 complete polynomial bindings.',flush=True)
        if not args.quick:
            import sympy
            receipt['software']={'python':'.'.join(map(str,sys.version_info[:3])),'sympy':sympy.__version__}
            commands=[];reproduced=[]
            with tempfile.TemporaryDirectory(prefix='con_zfc_wave3_verify_') as td:
                copy=Path(td)/'package'
                # Only mathematical payload is copied, not PDFs, caches or verifier outputs.
                copy.mkdir()
                for folder in ['amalgamation','arithmetic','domains','coefficients','review']:
                    shutil.copytree(ROOT/folder,copy/folder,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
                shutil.copy2(ROOT/'instance_binding.py',copy/'instance_binding.py')
                shutil.copy2(ROOT/'INSTANCE.json',copy/'INSTANCE.json')
                for script,extra,outputs in REPLAYS:
                    command=run(copy,script,extra)
                    for filename in outputs:
                        require(digest(copy/filename)==digest(ROOT/filename),'Byte-for-byte reproducibility failure: '+filename)
                        reproduced.append(filename)
                    command['byte_identical_outputs']=outputs;commands.append(command)
                # A separate nonmaterializing independent audit must agree with the
                # full audit, which was already rebuilt and compared above.
                command=run(copy,'coefficients/audit_compact.py',[])
                original=read(ROOT/'coefficients/independent_audit.json');normal=read(copy/'coefficients/independent_audit.json')
                original.pop('expanded',None)
                require(normal==original,'separate compact audit does not agree')
                command['matches_materializing_audit_on_all_nonexpansion_fields']=True;commands.append(command)
                require(packets(copy)==receipt['shipped_packets'],'post-replay packet checks')
                require(coefficients(copy)==receipt['coefficient_checks'],'post-replay numeric checks')
                require(transitions(copy)==receipt['literal_transition_check'],'post-replay transition checks')
            receipt['replay_commands']=commands
            receipt['byte_identical_rebuilt_files']=sorted(set(reproduced))
            receipt['upstream_python_executed']=False
            receipt['original_artifacts_overwritten']=False
        receipt['status']='PASS'
    except Exception as error:
        receipt['status']='FAIL';receipt['error']=str(error)
        output.write_text(json.dumps(receipt,indent=2)+'\n')
        raise
    output.write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS: '+output.name,flush=True)

if __name__=='__main__':main()
