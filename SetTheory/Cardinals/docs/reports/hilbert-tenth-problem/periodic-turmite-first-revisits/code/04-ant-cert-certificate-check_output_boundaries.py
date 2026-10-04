#!/usr/bin/env python3
"""Fresh recovered-output tests; only temporary directories are written."""
if not __debug__:raise RuntimeError('Optimized Python unsupported')
import importlib.util,json,pathlib,sys,tempfile,subprocess
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parent

def check():
    spec=importlib.util.spec_from_file_location('recovered_output_guards',ROOT/'merged_source.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    with tempfile.TemporaryDirectory(prefix='ant-recovered-guards-')as td:
        t=pathlib.Path(td);(t/'existing').write_text('preserve');(t/'alias').symlink_to(ROOT,target_is_directory=True);(t/'broken').symlink_to(t/'missing')
        cases=[('receipt_inside',lambda:m.output_paths(ROOT/'must-not-create.json')),('emit_inside',lambda:m.output_paths(t/'new1',ROOT/'must-not-emit.jsonl')),('existing_receipt',lambda:m.output_paths(t/'existing')),('existing_emit',lambda:m.output_paths(t/'new2',t/'existing')),('same_target',lambda:m.output_paths(t/'same',t/'same')),('symlink_source_receipt',lambda:m.output_paths(t/'alias'/'must-not-create.json')),('symlink_source_emit',lambda:m.output_paths(t/'new3',t/'alias'/'must-not-emit.jsonl')),('dangling_symlink',lambda:m.output_paths(t/'broken'))]
        rejected=[]
        for name,fn in cases:
            try:fn()
            except(ValueError,FileExistsError):rejected.append(name)
            else:raise RuntimeError('Unsafe output admitted: '+name)
        if (t/'existing').read_text()!='preserve':raise RuntimeError('Overwritten file')
        if any((t/x).exists()for x in ['new1','new2','new3','same']):raise RuntimeError('Preflight write')
        if m.output_paths(t/'good',t/'good-emit')!=[t/'good',t/'good-emit']:raise RuntimeError('Fresh valid pair rejected')
        run=subprocess.run([sys.executable,'-I','-B','-O',str(ROOT/'merged_source.py'),'--output',str(t/'optimized-output')],capture_output=True,text=True)
        if run.returncode==0 or (t/'optimized-output').exists():raise RuntimeError('Optimized run not rejected before output')
        return {'status':'PASS_RECOVERED_OUTPUT_BOUNDARIES','cases_rejected':rejected,'preflight_created_nothing':True,'existing_file_unchanged':True,'fresh_external_pair_admitted':True,'optimized_python_rejected_before_output':True}
if __name__=='__main__':print(json.dumps(check(),indent=2))
