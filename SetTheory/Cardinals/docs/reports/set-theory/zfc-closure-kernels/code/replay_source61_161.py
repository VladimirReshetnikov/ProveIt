from pathlib import Path
import os,subprocess,time,json
s=Path('/tmp/zfc-intake-161');t=time.monotonic();env=dict(os.environ);env.pop('PYTHONOPTIMIZE',None)
with (s/'run61-stdout.log').open('w') as out,(s/'run61-stderr.log').open('w') as err:
 p=subprocess.run(['python3','-B','code/verify.py'],cwd=s/'run61',env=env,stdout=out,stderr=err,timeout=300)
(s/'run61-replay.json').write_text(json.dumps(dict(exit_code=p.returncode,seconds=time.monotonic()-t,command=['python3','-B','code/verify.py'],cwd=str(s/'run61'),scope='Fresh executable suite; no Lean invocation or checksum-manifest check.'),indent=2)+'\n')
print('exit',p.returncode,'seconds',time.monotonic()-t)
raise SystemExit(p.returncode)
