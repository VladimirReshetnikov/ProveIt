#!/usr/bin/env python3
"""Bind observed process-log hash and inspect the pinned bit matrix definition."""
import hashlib,json,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';PACKET=BASE/'reviews/ipra-selected-native-bit-guarded-author';SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
terminal=PACKET/'terminal-observation.json';log=PACKET/'process.log';state=PACKET/'state.json';manifest=J(SNAP/'manifest.json')
assert H(terminal)=='2bed8ecd040bced7be3875a39c09055f99b62ddb4be3a863da8ca86338de4a6e';obs=J(terminal)
def bind(o):
 if o['observed_exit_code']!=0 or o['tool_session_id']!=40051 or o['process_log_sha256']!=H(log) or o['state_sha256']!=H(state):raise ValueError('terminal link mismatch')
bind(obs)
for field in ('process_log_sha256','state_sha256'):
 changed=dict(obs);changed[field]='0'*64
 try:bind(changed)
 except ValueError:pass
 else:raise AssertionError(('terminal link mutation accepted',field))
source=SNAP/'src/DiophantineConsistency/IPRACharacteristicTransfer.lean'
assert H(source)==manifest['sources']['DiophantineConsistency.IPRACharacteristicTransfer']['sha256']
text=source.read_text();a=text.split('def bitMatrix {n : ℕ} (c : Code n) : Semisentence language n :=',1);assert len(a)==2
body=' '.join(a[1].split('def transferBit',1)[0].split())
assert body=='(.rel .eq ![applyCode c (vars n), applyCode (.zero 0) Fin.elim0]) ⋎ (.rel .eq ![applyCode c (vars n), applyCode oneCode Fin.elim0])'
files=[Path(__file__),terminal,log,state,source,SNAP/'manifest.json'];before={str(p.resolve()):H(p) for p in files};assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_NATIVE_BIT_TERMINAL_AND_MATRIX_BINDING','inputs_sha256':before,'scope':'Finite terminal hash and bit-matrix source inspection only; no replay, arbitrary-checker or PDF claim.'};p=HERE/'terminal-bit-receipt.json'
if p.exists():raise ValueError('refusing to overwrite receipt')
p.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(p))
