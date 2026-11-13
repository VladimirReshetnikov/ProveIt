# Historical AQ22 paired extension: launch checklist

This is a pending procedure, not a record of a successful real run. During
preparation of this runbook, the real
parent pair was still `RUNNING`, with only the author exit recorded. **Do not
execute the launch until both parent builds, their comparison, and the
original coordinator's exit and stdout have been independently observed.** A
completed state file alone is not an observation of the coordinator exit.
Preserve the actual observation and its independently recorded digest; do not
construct one from the state file.

The parent snapshot is `/tmp/ipra-aq29-fresh-source-closure-v2`, manifest
SHA-256 `63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48`,
Git commit `74f797792c2ef3f81bc9d9e8eb14a58664a3aded`, and 1,210 source
rows. The provisional graph survey used 1,209 of those rows and all 37 pinned
additions; the source freezer must still retain all 1,210 parent rows. The
survey did not authenticate the parent source bytes or workspace drift. The
policy SHA-256 is
`0d80d3899a9b0d2356e16e4c7cc81ec72fe792ea1a1ee2e336f3e92373b4a6b1`.
These observations can become stale after another commit or file change.
The omitted closure row is the old target `IPRAAQ29NativeChecks`; it is not
imported by these additions, but the parent comparison, source freeze, and
sibling seed verification still require and check it.

The following commands are intended to be run sequentially from the repository
root, in one shell after the independently observed parent result is available.
Set the first three variables from that evidence, not by inventing or editing
an observation. The observation JSON must be the output of the original
coordinator observer and contain `observed_exit_code`, `observed_stdout`,
`pair_state_sha256`, and `pair_state_path` as required by
`prepare.check_parent_observation`. Use a fresh output directory and retain
all logs and receipts. Stop on any failure; never overwrite a failed run.

```bash
set -euo pipefail
export AQ22_OBSERVATION=/absolute/path/to/original-parent-observation.json
export AQ22_OBSERVATION_SHA256=REPLACE_WITH_INDEPENDENTLY_RECORDED_SHA256
export AQ22_PARENT_PAIR_SHA256=REPLACE_WITH_INDEPENDENTLY_RECORDED_SHA256
export AQ22_OLD=/tmp/ipra-aq29-fresh-source-closure-v2
export AQ22_PARENT=/tmp/ipra-aq29-fresh-project-pair
export AQ22_OLD_SHA256=63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48
export AQ22_TOOLS="$PWD/Computability/DiophantineConsistency/research/ipra-standard-aq22/historical"
export AQ22_RUN=/tmp/ipra-aq22-historical-paired-run-01

# Gate before creating anything: authenticate the separately observed parent
# exit, both recorded process exits and logs, tool hashes, and a fresh
# independent parent comparison. This may read substantial existing data.
python3 - <<'PY'
import importlib.util, json, os, sys
from pathlib import Path
h=Path(os.environ['AQ22_TOOLS']);sys.path.insert(0,str(h));import prepare
old=Path(os.environ['AQ22_OLD']).resolve(strict=True)
parent=Path(os.environ['AQ22_PARENT']).resolve(strict=True)
obs=Path(os.environ['AQ22_OBSERVATION']).resolve(strict=True)
pairpath=parent/'pair-state.json'
if prepare.digest(old/'manifest.json')!=os.environ['AQ22_OLD_SHA256']:raise ValueError('parent snapshot pin')
if prepare.digest(obs)!=os.environ['AQ22_OBSERVATION_SHA256']:raise ValueError('observation pin')
if prepare.digest(pairpath)!=os.environ['AQ22_PARENT_PAIR_SHA256']:raise ValueError('pair pin')
m=json.loads((old/'manifest.json').read_text()); pair=json.loads(pairpath.read_text())
prepare.check_parent_observation(json.loads(obs.read_text()),prepare.digest(pairpath),pairpath,len(m['order']))
if pair['status']!='MATCHED_PASS' or pair['snapshot_sha256']!=prepare.digest(old/'manifest.json'):
    raise ValueError('parent did not match this snapshot')
if [(r['label'],r['exit']) for r in pair['runs']]!=[('author',0),('peer',0)]:raise ValueError('parent exits')
for row in pair['runs']:
    if prepare.digest(row['process_log'])!=row['process_log_sha256'] or prepare.digest(parent/row['label']/'state.json')!=row['builder_state_sha256']:
        raise ValueError('parent process evidence drift')
for f,key in (('rebuild.py','driver_sha256'),('compare.py','comparator_sha256'),('run_pair.py','coordinator_sha256')):
    if prepare.digest(prepare.PAIR_TOOLS/f)!=pair[key]:raise ValueError('parent tool drift')
spec=importlib.util.spec_from_file_location('parent_compare',prepare.PAIR_TOOLS/'compare.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
comparison=mod.compare(parent/'author/state.json',parent/'peer/state.json')
if comparison!=pair['comparison'] or comparison['status']!='MATCHED_PASS':raise ValueError('parent comparison')
print('AUTHENTICATED_PARENT',len(m['order']),'rows; current clean Git HEAD',prepare.verify_current_git(m))
PY

mkdir "$AQ22_RUN"
python3 "$AQ22_TOOLS/../paired_plan.py" --snapshot "$AQ22_OLD" \
  --parent-sha256 "$AQ22_OLD_SHA256" --basis historical --output "$AQ22_RUN/strict-plan.json"
export AQ22_PLAN_SHA256="$(sha256sum "$AQ22_RUN/strict-plan.json" | cut -d' ' -f1)"

# Capture the actual freezer return code and stdout, not a reconstructed one.
python3 - <<'PY'
import hashlib,json,os,subprocess,sys
from pathlib import Path
e=os.environ;t=Path(e['AQ22_TOOLS']);r=Path(e['AQ22_RUN']);snapshot=r/'snapshot'
cmd=[sys.executable,str(t/'freeze.py'),'--old-snapshot',e['AQ22_OLD'],'--old-sha256',e['AQ22_OLD_SHA256'],
 '--strict-plan',str(r/'strict-plan.json'),'--strict-plan-sha256',e['AQ22_PLAN_SHA256'],
 '--parent',e['AQ22_PARENT'],'--parent-pair-sha256',e['AQ22_PARENT_PAIR_SHA256'],
 '--parent-observation',e['AQ22_OBSERVATION'],'--parent-observation-sha256',e['AQ22_OBSERVATION_SHA256'],
 '--output',str(snapshot)]
p=subprocess.run(cmd,capture_output=True,text=True);print(p.stdout,end='');print(p.stderr,end='',file=sys.stderr)
with (r/'freezer-process.json').open('x') as f:json.dump({'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr},f,indent=2)
if p.returncode:sys.exit(p.returncode)
digest=hashlib.sha256((snapshot/'manifest.json').read_bytes()).hexdigest()
with (r/'freezer-observation.json').open('x') as f:
 json.dump({'observed_exit_code':p.returncode,'observed_stdout':p.stdout,'snapshot_manifest_sha256':digest,'snapshot_path':str(snapshot)},f,indent=2)
PY
export AQ22_NEW_SHA256="$(sha256sum "$AQ22_RUN/snapshot/manifest.json" | cut -d' ' -f1)"
export AQ22_FREEZER_OBS_SHA256="$(sha256sum "$AQ22_RUN/freezer-observation.json" | cut -d' ' -f1)"
# Capture the actual preparer return code and both output streams on failure too.
python3 - <<'PY_PREPARE'
import json,os,subprocess,sys
from pathlib import Path
e=os.environ;t=Path(e['AQ22_TOOLS']);r=Path(e['AQ22_RUN'])
cmd=[sys.executable,str(t/'prepare.py'),'--parent',e['AQ22_PARENT'],'--old-snapshot',e['AQ22_OLD'],
 '--new-snapshot',str(r/'snapshot'),'--old-sha256',e['AQ22_OLD_SHA256'],'--new-sha256',e['AQ22_NEW_SHA256'],
 '--parent-pair-sha256',e['AQ22_PARENT_PAIR_SHA256'],'--parent-observation',e['AQ22_OBSERVATION'],
 '--parent-observation-sha256',e['AQ22_OBSERVATION_SHA256'],'--freezer-observation',str(r/'freezer-observation.json'),
 '--freezer-observation-sha256',e['AQ22_FREEZER_OBS_SHA256'],'--output',str(r/'prepared')]
p=subprocess.run(cmd,capture_output=True,text=True);print(p.stdout,end='');print(p.stderr,end='',file=sys.stderr)
with (r/'preparer-process.json').open('x') as f:
 json.dump({'observed_exit_code':p.returncode,'observed_stdout':p.stdout,'observed_stderr':p.stderr},f,indent=2)
if p.returncode:sys.exit(p.returncode)
PY_PREPARE
# Preparation records both HEADs; require them to agree before starting Lean.
python3 - <<'PY'
import json,os
from pathlib import Path
p=json.loads((Path(os.environ['AQ22_RUN'])/'prepared/preparation.json').read_text())
if p['workspace_head_before']!=p['workspace_head_after']:
 raise ValueError('workspace HEAD changed during preparation; preserve evidence and restart with fresh paths')
PY
export AQ22_PREP_SHA256="$(sha256sum "$AQ22_RUN/prepared/preparation.json" | cut -d' ' -f1)"

# Capture the real coordinator result and output even on failure.
python3 - <<'PY'
import hashlib,json,os,subprocess,sys
from pathlib import Path
e=os.environ;t=Path(e['AQ22_TOOLS']);r=Path(e['AQ22_RUN']);pair=r/'pair'
cmd=[sys.executable,str(t/'run_pair.py'),'--prepared',str(r/'prepared'),'--preparation-sha256',e['AQ22_PREP_SHA256'],
 '--old-snapshot',e['AQ22_OLD'],'--new-snapshot',str(r/'snapshot'),'--expected-axiom-reports','3','--output',str(pair)]
p=subprocess.run(cmd,capture_output=True,text=True);print(p.stdout,end='');print(p.stderr,end='',file=sys.stderr)
state=pair/'pair-state.json';sha=hashlib.sha256(state.read_bytes()).hexdigest() if state.is_file() else None
with (r/'pair-observation.json').open('x') as f:
 json.dump({'observed_exit_code':p.returncode,'observed_stdout':p.stdout,'observed_stderr':p.stderr,'pair_state_sha256':sha,'pair_state_path':str(state)},f,indent=2)
if p.returncode:sys.exit(p.returncode)
PY
```

Afterward, retain and independently inspect the coordinator observation,
`pair-state.json`, both builder states and logs, snapshot, strict plan, and
preparation receipt and separately observed preparer exit. Require actual outer exit 0, final stdout
`MATCHED_SELECTIVE_PASS 37 affected modules`, paired status
`MATCHED_SELECTIVE_PASS`, sibling exits 0, historical basis, exact 37 additions
and their 94 diagnostics, and reproducibility of the comparator using
`python3 "$AQ22_TOOLS/compare.py" "$AQ22_RUN/prepared" "$AQ22_OLD" "$AQ22_RUN/snapshot" "$AQ22_PREP_SHA256"`.
Reconfirm all pins after comparison. Record separately the outcome of this
independent validation; do not infer it from the coordinator's state alone.

The freezer pins additions and policy to the Git commit at freezing; their
workspace bytes must continue to match. Parent sources are taken from the
frozen historical commit, although their current workspace versions may differ
if tracked and clean. A later unrelated commit can be acceptable between
stages if checks pass; the freezer rejects a HEAD change during freezing.
Preparation records its before/after HEADs; the explicit gate above rejects a
change during that stage. Regenerate a strict plan after a HEAD change before
freezing. A successful result is historical-parent evidence, not a current
source claim or proof that the desired internal PRA equivalence is established.
Package-transitive, dynamic and transient-mutation ancestry remains outside the
guards, as does the missing outer Foundation-wrapper exit observation.
