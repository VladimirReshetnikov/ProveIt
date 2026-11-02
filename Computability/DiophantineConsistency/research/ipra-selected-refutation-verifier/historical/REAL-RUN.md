# Historical SELECTED_CHECKER paired extension: launch checklist

This is a pending procedure, not a record of a successful real run. Do not
launch it until this selected-checker workflow is independently audited, including
its full report policy and toy controls, and until the separate SELECTED_CHECKER guarded
author artifact audit has passed. Both receipts and actual audit process exits
must be independently recorded. The original parent pair has completed
and its separate artifact audit passed; verify both recorded terminal exits and
receipts before starting. Never infer an actual process exit from a state file.

The parent snapshot is `/tmp/ipra-aq29-fresh-source-closure-v2`, manifest
SHA-256 `63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48`,
Git commit `74f797792c2ef3f81bc9d9e8eb14a58664a3aded`, and 1,210 source
rows. The provisional graph survey used 1,096 of those rows and all ten pinned
additions; the source freezer must still retain all 1,210 parent rows. The
survey did not authenticate the parent source bytes or workspace drift. The
policy SHA-256 is
`e4361ca7aa1032a2391cbd1cce6bded47a2fa993794050accdda5aa3e36b48c9`.
These observations can become stale after another commit or file change.
The closure survey omits 114 parent rows, including the old terminal checks.
The parent comparison, source freeze, and sibling seed verification still
require and check all 1,210 parent rows.

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
export SELECTED_CHECKER_WORKFLOW_AUDIT=/absolute/path/to/selected-checker-workflow-audit-receipt.json
export SELECTED_CHECKER_WORKFLOW_TERMINAL=/absolute/path/to/selected-checker-workflow-audit-terminal.json
export SELECTED_CHECKER_WORKFLOW_AUDIT_SHA256=REPLACE_WITH_INDEPENDENTLY_RECORDED_SHA256
export SELECTED_CHECKER_AUTHOR_AUDIT="$PWD/Computability/DiophantineConsistency/reviews/ipra-selected-verifier-guarded-author-independent-audit/receipt.json"
export SELECTED_CHECKER_AUTHOR_TERMINAL="$PWD/Computability/DiophantineConsistency/reviews/ipra-selected-verifier-guarded-author-independent-audit/terminal-observation.json"
export SELECTED_CHECKER_AUTHOR_AUDIT_SHA256=4f6887fb9549837719008fdc53444f5e6843231d97bbe30e795cd2da4b42c95d
export SELECTED_CHECKER_AUTHOR_TERMINAL_SHA256=0dd2cf5e58c3b98c118188ee4aca193dca18e56f61d659649fa33601290f0ca3
export SELECTED_CHECKER_OBSERVATION=/absolute/path/to/original-parent-observation.json
export SELECTED_CHECKER_OBSERVATION_SHA256=REPLACE_WITH_INDEPENDENTLY_RECORDED_SHA256
export SELECTED_CHECKER_PARENT_PAIR_SHA256=REPLACE_WITH_INDEPENDENTLY_RECORDED_SHA256
export SELECTED_CHECKER_AUDIT_RECEIPT="$PWD/Computability/DiophantineConsistency/reviews/fresh-project-pair-independent-audit/receipt.json"
export SELECTED_CHECKER_AUDIT_TERMINAL="$PWD/Computability/DiophantineConsistency/reviews/fresh-project-pair-independent-audit/terminal-observation.json"
export SELECTED_CHECKER_AUDIT_RECEIPT_SHA256=b9c77761c2944dc83b02595db874874432280903fe1c527754f0cdc858b5142e
export SELECTED_CHECKER_OLD=/tmp/ipra-aq29-fresh-source-closure-v2
export SELECTED_CHECKER_PARENT=/tmp/ipra-aq29-fresh-project-pair
export SELECTED_CHECKER_OLD_SHA256=63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48
export SELECTED_CHECKER_TOOLS="$PWD/Computability/DiophantineConsistency/research/ipra-selected-refutation-verifier/historical"
export SELECTED_CHECKER_RUN=/tmp/ipra-selected-checker-historical-paired-run-01

# Check the two authenticated tracked package paths before planning.
python3 "$SELECTED_CHECKER_TOOLS/check_package_choice.py"

# Gate before creating anything: authenticate the separately observed parent
# exit, both recorded process exits and logs, tool hashes, and a fresh
# independent parent comparison. This may read substantial existing data.
python3 - <<'PY'
import importlib.util, json, os, sys
from pathlib import Path
h=Path(os.environ['SELECTED_CHECKER_TOOLS']);sys.path.insert(0,str(h));import prepare
wfpath=Path(os.environ['SELECTED_CHECKER_WORKFLOW_AUDIT']).resolve(strict=True)
wfterminal=Path(os.environ['SELECTED_CHECKER_WORKFLOW_TERMINAL']).resolve(strict=True)
wf=json.loads(wfpath.read_text()); wft=json.loads(wfterminal.read_text())
if prepare.digest(wfpath)!=os.environ['SELECTED_CHECKER_WORKFLOW_AUDIT_SHA256'] or wft['receipt_sha256']!=prepare.digest(wfpath):raise ValueError('workflow audit receipt pin')
if wft['observed_exit_code']!=0 or wf['status']!='PASS_INDEPENDENT_SELECTED_CHECKER_WORKFLOW_REVIEW' or wf['modules']!=10 or wf['reports']!=16:
    raise ValueError('independent SELECTED_CHECKER workflow review missing or mismatched')
for name in ('task-policy.json','prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py',
             'run_controls.py','test_history.py','test_prepare.py','test_freeze.py',
             'test_real_extension.py','test_full_chain.py','test_real_policy.py','check_package_choice.py','test_package_choice.py',
             'test_author_ancestry_gate.py','policy-preflight.py','REAL-RUN.md','../paired_plan.py',
             '../author-additions.json'):
    f=(h/name).resolve(strict=True)
    if wf['inputs_sha256'].get(str(f))!=prepare.digest(f):raise ValueError(('reviewed workflow input changed',name))
authorpath=Path(os.environ['SELECTED_CHECKER_AUTHOR_AUDIT']).resolve(strict=True)
authorterminal=Path(os.environ['SELECTED_CHECKER_AUTHOR_TERMINAL']).resolve(strict=True)
if prepare.digest(authorterminal)!=os.environ['SELECTED_CHECKER_AUTHOR_TERMINAL_SHA256']:raise ValueError('author audit terminal pin')
author=json.loads(authorpath.read_text()); autht=json.loads(authorterminal.read_text())
if prepare.digest(authorpath)!=os.environ['SELECTED_CHECKER_AUTHOR_AUDIT_SHA256'] or autht['receipt_sha256']!=prepare.digest(authorpath):raise ValueError('author audit receipt pin')
if autht['observed_exit_code']!=0 or author['status']!='PASS_INDEPENDENT_SELECTED_CHECKER_AUTHOR_ARTIFACT_AUDIT':raise ValueError('independent SELECTED_CHECKER author audit missing')
if author['manifest_sha256']!='dae80b2f3bc452f6138da34e5af026c458c7464bdee1b9a1bb9e0d02ca70a7c2' or author['trial_state_sha256']!='385b40c10de33c60da377b0b84ba22ee2c9103e2a32d8dffc25e84857c26af30':raise ValueError('SELECTED_CHECKER author audit wrong run')
if author['parent_state_sha256']!='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153' or author['added_modules']!=10 or author['added_direct_import_edges']!=35:raise ValueError('SELECTED_CHECKER author audit wrong ancestry')
old=Path(os.environ['SELECTED_CHECKER_OLD']).resolve(strict=True)
parent=Path(os.environ['SELECTED_CHECKER_PARENT']).resolve(strict=True)
obs=Path(os.environ['SELECTED_CHECKER_OBSERVATION']).resolve(strict=True)
pairpath=parent/'pair-state.json'
if prepare.digest(old/'manifest.json')!=os.environ['SELECTED_CHECKER_OLD_SHA256']:raise ValueError('parent snapshot pin')
if prepare.digest(obs)!=os.environ['SELECTED_CHECKER_OBSERVATION_SHA256']:raise ValueError('observation pin')
if prepare.digest(pairpath)!=os.environ['SELECTED_CHECKER_PARENT_PAIR_SHA256']:raise ValueError('pair pin')
m=json.loads((old/'manifest.json').read_text()); pair=json.loads(pairpath.read_text())
auditpath=Path(os.environ['SELECTED_CHECKER_AUDIT_RECEIPT']).resolve(strict=True)
audit_terminal=Path(os.environ['SELECTED_CHECKER_AUDIT_TERMINAL']).resolve(strict=True)
audit=json.loads(auditpath.read_text()); terminal=json.loads(audit_terminal.read_text())
if prepare.digest(auditpath)!=os.environ['SELECTED_CHECKER_AUDIT_RECEIPT_SHA256'] or terminal['receipt_sha256']!=prepare.digest(auditpath):
    raise ValueError('independent parent audit receipt pin')
if terminal['exit_code']!=0 or audit['status']!='PASS_INDEPENDENT_PAIRED_ARTIFACT_AUDIT' or audit['pair_state_sha256']!=prepare.digest(pairpath):
    raise ValueError('independent parent audit missing or mismatched')
if audit['peer_state_sha256']!=prepare.digest(parent/'peer/state.json'):
    raise ValueError('independent parent audit peer mismatch')
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

mkdir "$SELECTED_CHECKER_RUN"
python3 "$SELECTED_CHECKER_TOOLS/../paired_plan.py" --snapshot "$SELECTED_CHECKER_OLD" \
  --parent-sha256 "$SELECTED_CHECKER_OLD_SHA256" --basis historical --output "$SELECTED_CHECKER_RUN/strict-plan.json"
export SELECTED_CHECKER_PLAN_SHA256="$(sha256sum "$SELECTED_CHECKER_RUN/strict-plan.json" | cut -d' ' -f1)"

# Capture the actual freezer return code and stdout, not a reconstructed one.
python3 - <<'PY'
import hashlib,json,os,subprocess,sys
from pathlib import Path
e=os.environ;t=Path(e['SELECTED_CHECKER_TOOLS']);r=Path(e['SELECTED_CHECKER_RUN']);snapshot=r/'snapshot'
cmd=[sys.executable,str(t/'freeze.py'),'--old-snapshot',e['SELECTED_CHECKER_OLD'],'--old-sha256',e['SELECTED_CHECKER_OLD_SHA256'],
 '--strict-plan',str(r/'strict-plan.json'),'--strict-plan-sha256',e['SELECTED_CHECKER_PLAN_SHA256'],
 '--parent',e['SELECTED_CHECKER_PARENT'],'--parent-pair-sha256',e['SELECTED_CHECKER_PARENT_PAIR_SHA256'],
 '--parent-observation',e['SELECTED_CHECKER_OBSERVATION'],'--parent-observation-sha256',e['SELECTED_CHECKER_OBSERVATION_SHA256'],
 '--output',str(snapshot)]
p=subprocess.run(cmd,capture_output=True,text=True);print(p.stdout,end='');print(p.stderr,end='',file=sys.stderr)
with (r/'freezer-process.json').open('x') as f:json.dump({'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr},f,indent=2)
if p.returncode:sys.exit(p.returncode)
digest=hashlib.sha256((snapshot/'manifest.json').read_bytes()).hexdigest()
with (r/'freezer-observation.json').open('x') as f:
 json.dump({'observed_exit_code':p.returncode,'observed_stdout':p.stdout,'snapshot_manifest_sha256':digest,'snapshot_path':str(snapshot)},f,indent=2)
PY
export SELECTED_CHECKER_NEW_SHA256="$(sha256sum "$SELECTED_CHECKER_RUN/snapshot/manifest.json" | cut -d' ' -f1)"
export SELECTED_CHECKER_FREEZER_OBS_SHA256="$(sha256sum "$SELECTED_CHECKER_RUN/freezer-observation.json" | cut -d' ' -f1)"
# Capture the actual preparer return code and both output streams on failure too.
python3 - <<'PY_PREPARE'
import json,os,subprocess,sys
from pathlib import Path
e=os.environ;t=Path(e['SELECTED_CHECKER_TOOLS']);r=Path(e['SELECTED_CHECKER_RUN'])
cmd=[sys.executable,str(t/'prepare.py'),'--parent',e['SELECTED_CHECKER_PARENT'],'--old-snapshot',e['SELECTED_CHECKER_OLD'],
 '--new-snapshot',str(r/'snapshot'),'--old-sha256',e['SELECTED_CHECKER_OLD_SHA256'],'--new-sha256',e['SELECTED_CHECKER_NEW_SHA256'],
 '--parent-pair-sha256',e['SELECTED_CHECKER_PARENT_PAIR_SHA256'],'--parent-observation',e['SELECTED_CHECKER_OBSERVATION'],
 '--parent-observation-sha256',e['SELECTED_CHECKER_OBSERVATION_SHA256'],'--freezer-observation',str(r/'freezer-observation.json'),
 '--freezer-observation-sha256',e['SELECTED_CHECKER_FREEZER_OBS_SHA256'],'--output',str(r/'prepared')]
p=subprocess.run(cmd,capture_output=True,text=True);print(p.stdout,end='');print(p.stderr,end='',file=sys.stderr)
with (r/'preparer-process.json').open('x') as f:
 json.dump({'observed_exit_code':p.returncode,'observed_stdout':p.stdout,'observed_stderr':p.stderr},f,indent=2)
if p.returncode:sys.exit(p.returncode)
PY_PREPARE
# Preparation records both HEADs; require them to agree before starting Lean.
python3 - <<'PY'
import json,os
from pathlib import Path
p=json.loads((Path(os.environ['SELECTED_CHECKER_RUN'])/'prepared/preparation.json').read_text())
if p['workspace_head_before']!=p['workspace_head_after']:
 raise ValueError('workspace HEAD changed during preparation; preserve evidence and restart with fresh paths')
PY
export SELECTED_CHECKER_PREP_SHA256="$(sha256sum "$SELECTED_CHECKER_RUN/prepared/preparation.json" | cut -d' ' -f1)"

# Capture the real coordinator result and output even on failure.
python3 - <<'PY'
import hashlib,json,os,subprocess,sys
from pathlib import Path
e=os.environ;t=Path(e['SELECTED_CHECKER_TOOLS']);r=Path(e['SELECTED_CHECKER_RUN']);pair=r/'pair'
cmd=[sys.executable,str(t/'run_pair.py'),'--prepared',str(r/'prepared'),'--preparation-sha256',e['SELECTED_CHECKER_PREP_SHA256'],
 '--old-snapshot',e['SELECTED_CHECKER_OLD'],'--new-snapshot',str(r/'snapshot'),'--expected-axiom-reports','1','--output',str(pair)]
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
`MATCHED_SELECTIVE_PASS 10 affected modules`, paired status
`MATCHED_SELECTIVE_PASS`, sibling exits 0, historical basis, exact ten additions
and all 16 diagnostics (eight for square-sums, five for product, two for the matrix, and one for the checker), and reproducibility of the comparator using
`python3 "$SELECTED_CHECKER_TOOLS/compare.py" "$SELECTED_CHECKER_RUN/prepared" "$SELECTED_CHECKER_OLD" "$SELECTED_CHECKER_RUN/snapshot" "$SELECTED_CHECKER_PREP_SHA256"`.
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
