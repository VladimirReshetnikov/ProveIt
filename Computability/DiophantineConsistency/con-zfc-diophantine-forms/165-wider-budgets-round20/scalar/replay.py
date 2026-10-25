#!/usr/bin/env python3
"""Verify pinned bytes, then reproduce and independently audit in an isolated copy."""
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    manifest=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
    for row in manifest['files']:
        p=ROOT/row['path'];need(p.is_file() and p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],'sealed bytes '+row['path'])
    commands=[['-B','build.py','--check'],['-B','build.py'],
      ['-B','check.py','--receipt','CHECK.json'],['-B','-O','check.py','--receipt','CHECK_OPTIMIZED.json'],
      ['-B','audit_mutations.py'],['-B','-O','audit_mutations.py']]
    for deg,ops in [(298,147),(300,145)]:
        for opt in [False,True]:
            commands.append(['-B']+(['-O'] if opt else [])+['check_scalar_top_forms.py','--graph',f'integer11_degree{deg}_ops{ops}.json','--output',f'TOP_FORMS_{deg}'+('_OPTIMIZED' if opt else '')+'.json'])
    results=[]
    with tempfile.TemporaryDirectory(prefix='conzfc_round20_scalar_') as td:
        target=Path(td)/'scalar';shutil.copytree(ROOT,target,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        for cmd in commands:
            cp=subprocess.run([sys.executable]+cmd,cwd=target,text=True,capture_output=True)
            need(cp.returncode==0,'portable command '+str(cmd)+'\n'+cp.stdout+'\n'+cp.stderr)
            results.append({'command':cmd,'returncode':cp.returncode,'stdout_sha256':hashlib.sha256(cp.stdout.encode()).hexdigest()})
        for row in manifest['files']:
            need(digest(target/row['path'])==row['sha256'],'byte-identical replay '+row['path'])
    result={'status':'PASS','authenticated_files':len(manifest['files']),'portable_commands':results,
      'graphs_byte_identically_rebuilt':True,'receipts_byte_identically_rebuilt':True,
      'python_optimized_checks_pass':True,'no_network_or_external_project_files_required':True}
    (ROOT/'REPLAY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
