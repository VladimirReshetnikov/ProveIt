#!/usr/bin/env python3
"""Portable reconstruction and certificate replay for PA194AX11 and PA194QH5.

Default: rebuild both tables; check source splices, command algebra and graph
novelty; replay both independent literal-tape symbolic engines; compare fresh
receipts with the delivered full receipts. --quick omits only the independent
literal-tape replays and explicitly validates their pinned machine, source,
and certificate-file hashes. The construction symbolic checks still run.

Python3.10+ standard library only. This does not compile the report or claim a
new end-to-end Lean/Rocq theorem. All replay outputs use temporary directories;
only an explicitly supplied --receipt path is written outside them.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,tempfile,time

ROOT=Path(__file__).resolve().parent

def require(condition,message):
    if not condition:raise AssertionError(message)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):return json.loads(path.read_text())
def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,indent=2)+'\n')

def normalize_sites(value):
    return [[''.join(map(str,p))if isinstance(p,list)else p,op,a]for p,op,a in value]

def expand_grammar(value):
    rules=value['rules']
    def visit(node):
        if isinstance(node,str)and node in rules:return[visit(c)for c in rules[node]]
        return node
    return visit(value['root'])

def pinned_inputs():
    manifest_path=ROOT/'verification_inputs.json';manifest=read(manifest_path)
    require(manifest['schema']==1,'Unknown verification manifest schema.')
    for relative,digest in manifest['files'].items():
        path=ROOT/relative
        require(path.is_file(),'Pinned file is missing: '+relative)
        require(sha(path)==digest,'Pinned file hash differs: '+relative)
    bindings={}
    for family,directory in [('PA194AX11','primary'),('PA194QH5','secondary_qh5')]:
        machine=ROOT/directory/'machine';receipt=read(machine/'independent/receipt.json')
        require(receipt['status']=='PASS',family+' full receipt is not PASS.')
        require(receipt['dense_sha256']==sha(machine/'machine.tm'),family+' full receipt table hash differs.')
        require(receipt['native_sha256']==sha(machine/'machine.native.tm'),family+' full receipt native hash differs.')
        require(receipt['contracts_sha256']==sha(machine/'independent/contracts.json'),family+' contract evidence hash differs.')
        files={p:d for p,d in manifest['files'].items()if p.startswith(directory+'/machine/')}
        bindings[family]={'recorded_full_receipt':receipt,'pinned_machine_source_and_evidence':files}
    return {'manifest_sha256':sha(manifest_path),'pinned_files':len(manifest['files']),'families':bindings}

def main():
    parser=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--quick',action='store_true',help='Skip only independent literal-tape replays; validate their pinned full receipts and source/table hashes.')
    parser.add_argument('--receipt',type=Path,help='Write the structured combined result to this file.')
    args=parser.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without -O or PYTHONOPTIMIZE; certificate assertions must remain enabled.')
    result={'status':'RUNNING','mode':'quick'if args.quick else'full','independent_physical_replays':not args.quick,'kernel_checked':False,'stages':[]}
    started=time.monotonic()
    try:
        result['pinned_evidence']=pinned_inputs()
        print('Pinned machine/source/full-receipt hashes PASS',flush=True)
        with tempfile.TemporaryDirectory(prefix='pa194-research-verify-')as temporary:
            temp=Path(temporary)
            def run(label,script,*arguments):
                command=[sys.executable,'-B',str(ROOT/script),*map(str,arguments)]
                when=time.monotonic()
                completed=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
                entry={'name':label,'status':'PASS'if completed.returncode==0 else'FAIL','seconds':round(time.monotonic()-when,6)}
                result['stages'].append(entry)
                if completed.returncode:
                    entry['returncode']=completed.returncode
                    entry['stdout_tail']=completed.stdout[-6000:];entry['stderr_tail']=completed.stderr[-6000:]
                    raise RuntimeError(label+' failed.\n'+entry['stdout_tail']+'\n'+entry['stderr_tail'])
                print(label+' PASS',flush=True)
            # Separate processes intentionally isolate similarly named vendor modules.
            primary=temp/'primary';source_receipt=temp/'primary-source.json';command_receipt=temp/'primary-commands.json'
            run('PA194AX11 deterministic build and construction symbolic checks','primary/build.py','--output',primary)
            frozen=ROOT/'primary/machine'
            for name in ['machine.tm','machine.native.tm','raw.native.tm']:
                require((primary/name).read_bytes()==(frozen/name).read_bytes(),'Primary exact table rebuild differs: '+name)
            for name in ['labels.json','nodes.json','instructions.json','folds.json','local_folds.json','grammar.json']:
                require(read(primary/name)==read(frozen/name),'Primary reconstructed source/certificate differs: '+name)
            require(normalize_sites(read(primary/'sites.json'))==normalize_sites(read(frozen/'sites.json')),'Primary reconstructed source sites differ.')
            require(read(primary/'receipt.json')==read(frozen/'construction_receipt.json'),'Primary construction receipt differs.')
            tree=expand_grammar(read(primary/'grammar.json'))
            require(tree==read(frozen/'grammar.tree.json'),'Primary macro tree and compact grammar disagree.')
            write(primary/'grammar.tree.json',tree)
            run('PA194AX11 independent source-splice binding','primary/check_source.py','--machine',primary,'--output',source_receipt)
            require(read(source_receipt)==read(frozen/'source_binding.json'),'Primary source-binding receipt differs.')
            run('PA194AX11 eleven-entry command algebra and four-field scheduler','proof/ax11_commands.py','--machine',primary,'--output',command_receipt)
            require(read(command_receipt)==read(ROOT/'proof/commands_receipt.json'),'Primary command-algebra receipt differs.')
            result['primary']={'dense_sha256':sha(primary/'machine.tm'),'exact_table_rebuild':True,'exact_source_rebuild':True,'construction':read(primary/'receipt.json'),'source_binding':{k:v for k,v in read(source_receipt).items()if k!='relocation'},'commands':read(command_receipt),'independent_replay':not args.quick}
            if not args.quick:
                literal=temp/'primary-literal'
                run('PA194AX11 independent literal-tape replay','primary/verification/check_literal.py','--machine',primary,'--output',literal)
                fresh=read(literal/'receipt.json');recorded=read(frozen/'independent/receipt.json')
                require(fresh==recorded,'Primary independent full receipt differs.')
                for name in ['contracts.json','list_lemmas.json']:
                    require((literal/name).read_bytes()==(frozen/'independent'/name).read_bytes(),'Primary independent certificate differs: '+name)
                result['primary']['independent']=fresh
            secondary_receipt=temp/'secondary.json'
            secondary_arguments=['--receipt',secondary_receipt]
            if args.quick:secondary_arguments.append('--quick')
            run('PA194QH5 complete '+('quick'if args.quick else'full')+' verifier','secondary_qh5/verify.py',*secondary_arguments)
            result['secondary']=read(secondary_receipt)
            require(result['secondary']['status']=='PASS','Secondary verifier did not report PASS.')
            require(result['secondary']['independent_replay']==(not args.quick),'Secondary replay mode disagrees.')
            frontier=ROOT/'comparison/census/frontier_tables';novelty={}
            for family,candidate,oldfile in [('PA194AX11',primary/'machine.tm','axfall_novelty.json'),('PA194QH5',ROOT/'secondary_qh5/machine/machine.tm','qh5_novelty.json')]:
                output=temp/(family+'-novelty.json')
                run(family+' exact novelty against prior frontier','comparison/scanner/compare_novelty.py',candidate,frontier,'--output',output)
                fresh=read(output);recorded=read(ROOT/'comparison'/oldfile)
                require(fresh['candidate_sha256']==sha(candidate),family+' novelty input mismatch.')
                require(fresh['compared_classes']==76 and not fresh['excluded_no_spanning_root'],family+' novelty census scope changed.')
                require(fresh['distinct_from_all_recognized_classes']and not fresh['matches'],family+' repeats a prior graph.')
                require({k:v for k,v in fresh.items()if k!='candidate'}=={k:v for k,v in recorded.items()if k!='candidate'},family+' exact novelty receipt differs.')
                # Do not publish ephemeral paths in the portable combined result.
                fresh['candidate']='primary/machine/machine.tm'if family=='PA194AX11'else'secondary_qh5/machine/machine.tm'
                novelty[family]=fresh
            require(novelty['PA194AX11']['candidate_cosmetic_fingerprint']!=novelty['PA194QH5']['candidate_cosmetic_fingerprint'],'The two new machines have equal canonical graph fingerprints.')
            result['novelty']=novelty
        result['status']='PASS'
        result['scope']='Fresh construction symbolic checks, exact source and command binding, pinned recorded full physical evidence, and exact finite graph novelty. Independent physical replays are performed only in full mode. Mathematical PA calibration is documented in the report; no new kernel theorem is claimed.'
    except Exception as error:
        result['status']='FAIL';result['error']=str(error)
        result['elapsed_seconds']=round(time.monotonic()-started,6)
        if args.receipt:write(args.receipt,result)
        raise
    result['elapsed_seconds']=round(time.monotonic()-started,6)
    if args.receipt:write(args.receipt,result)
    print(json.dumps({'status':result['status'],'mode':result['mode'],'independent_physical_replays':result['independent_physical_replays'],'pinned_files':result['pinned_evidence']['pinned_files'],'machines':['PA194AX11','PA194QH5'],'novelty_classes_per_machine':76,'elapsed_seconds':result['elapsed_seconds']},indent=2),flush=True)
    return result

if __name__=='__main__':main()
