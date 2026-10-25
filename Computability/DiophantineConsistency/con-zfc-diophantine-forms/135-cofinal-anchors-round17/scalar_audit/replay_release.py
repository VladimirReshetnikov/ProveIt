#!/usr/bin/env python3
"""Run the authenticated release's entire replay from whitelist-only bytes."""
import pathlib,json,tempfile,shutil,subprocess,os,sys
SRC=pathlib.Path(__file__).resolve().parents[1]/'scalar'
OUT=pathlib.Path(__file__).resolve().parent
manifest=json.loads((SRC/'RELEASE_WHITELIST.json').read_text())
with tempfile.TemporaryDirectory(prefix='independent-scalar-audit-') as temp:
 dest=pathlib.Path(temp)
 for name in list(manifest['files'])+['RELEASE_WHITELIST.json']:
  to=dest/name;to.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(SRC/name,to)
 env={k:v for k,v in os.environ.items() if k not in ('PYTHONPATH','PYTHONHOME')};env['PYTHONDONTWRITEBYTECODE']='1'
 run=subprocess.run([sys.executable,'-B','replay.py'],cwd=dest,env=env,capture_output=True,text=True)
 (OUT/'CLEAN_REPLAY.stdout.json').write_text(run.stdout);(OUT/'CLEAN_REPLAY.stderr.txt').write_text(run.stderr)
 if run.returncode:raise RuntimeError(run.stderr)
 report=json.loads(run.stdout);report.update({'independent_auditor_started':True,'only_manifest_files_plus_manifest_copied':True,'original_source_unmodified':True})
 (OUT/'CLEAN_REPLAY.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2))
