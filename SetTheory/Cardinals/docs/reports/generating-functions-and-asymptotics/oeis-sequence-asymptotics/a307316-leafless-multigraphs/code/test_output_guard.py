#!/usr/bin/env python3
"""Selected pre-execution output rejection tests, all mutations isolated."""
import sys
sys.dont_write_bytecode=True
import json
from pathlib import Path
import subprocess
import tempfile
from hashlib import sha256
ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def main():
    protected=ROOT/'report131.tex'
    before=sha256(protected.read_bytes()).hexdigest()
    runs=0
    for mode in ([],['-O']):
        with tempfile.TemporaryDirectory(prefix='report131-output-test-') as td:
            work=Path(td)
            existing=work/'exists.txt'; existing.write_text('retain this\n')
            link=work/'link.txt'; link.symlink_to(existing)
            directory=work/'real'; directory.mkdir()
            alias=work/'alias'; alias.symlink_to(directory,target_is_directory=True)
            cases=[(protected,'OUTPUT_INSIDE_PACKAGE'),(existing,'OUTPUT_ALREADY_EXISTS'),
                   (link,'OUTPUT_SYMLINK'),(alias/'new.txt','OUTPUT_SYMLINK')]
            for script in ('build.py','repack.py','reproduce.py'):
                for output,diagnostic in cases:
                    args=[str(output)] if script=='repack.py' else ['--output',str(output)]
                    cp=subprocess.run([sys.executable,'-B',*mode,str(ROOT/script),*args],
                                      cwd=ROOT,capture_output=True,text=True,timeout=15)
                    require(cp.returncode!=0 and diagnostic in cp.stderr,
                            'OUTPUT_REJECTION_FAILED '+script+' '+diagnostic)
                    runs+=1
            require(existing.read_text()=='retain this\n','EXISTING_OUTPUT_CHANGED')
            require(not (directory/'new.txt').exists(),'SYMLINK_OUTPUT_CREATED')
    require(sha256(protected.read_bytes()).hexdigest()==before,'PACKAGE_SOURCE_CHANGED')
    print(json.dumps({'status':'PASS','scripts':3,'modes':['normal','optimized'],
                      'cases_per_script_and_mode':4,'negative_runs':runs,
                      'inputs_unchanged':True},sort_keys=True))

if __name__=='__main__':
    main()
