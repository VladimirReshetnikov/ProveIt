#!/usr/bin/env python3
"""Authenticate and independently rebuild/audit a clean, offline copy."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
def need(ok,msg):
    if not ok:raise ValueError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    manifest=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
    for row in manifest['files']:
        p=ROOT/row['path'];need(p.is_file() and p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],'sealed bytes '+row['path'])
    commands=[['-B','native4127/start_only.py'],['-B','-O','native4127/start_only.py'],['-B','build.py','--check'],['-B','build.py'],
      ['-B','verify.py','--receipt','CHECK.json'],
      ['-B','verify.py','--deep','--mutations','--receipt','CHECK_DEEP.json'],
      ['-B','-O','verify.py','--deep','--mutations','--receipt','CHECK_OPTIMIZED.json']]
    results=[]
    with tempfile.TemporaryDirectory(prefix='conzfc_round22_positive_') as td:
        target=Path(td)/'positive10';shutil.copytree(ROOT,target,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        for cmd in commands:
            cp=subprocess.run([sys.executable]+cmd,cwd=target,text=True,capture_output=True)
            need(cp.returncode==0,'portable command '+str(cmd)+'\n'+cp.stdout+'\n'+cp.stderr)
            results.append({'command':cmd,'returncode':cp.returncode,'stdout_sha256':hashlib.sha256(cp.stdout.encode()).hexdigest()})
        for row in manifest['files']:need(digest(target/row['path'])==row['sha256'],'byte-identical replay '+row['path'])
    result={'status':'PASS','authenticated_files':len(manifest['files']),'portable_commands':results,
      'graphs_byte_identically_rebuilt':True,'receipts_byte_identically_rebuilt':True,
      'python_optimized_checks_pass':True,'no_network_or_external_project_files_required':True}
    (ROOT/'REPLAY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
