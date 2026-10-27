from pathlib import Path
import hashlib, json, shutil

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
REV = DC / 'reviews'
PRIVATE = Path('/tmp/native-adaptive-power-tr0wfda0')
DRIVER = Path('/tmp/native-adaptive-power-driver.py')
BUNDLE = REV / 'native-adaptive-power-recovery-replay'
PACKET = REV / 'native-adaptive-power-recovery-replay.json'
MANIFEST = REV / 'native-adaptive-power-recovery-replay-files.json'

def record(path):
    p = Path(path)
    b = p.read_bytes()
    return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))

def check(pin):
    r=record(pin['path'])
    if r['sha256']!=pin['sha256'] or r['bytes']!=pin['bytes']:
        raise RuntimeError('Changed pin '+pin['path'])

if BUNDLE.exists() or PACKET.exists() or MANIFEST.exists():
    raise RuntimeError('Refusing to replace frozen evidence')
if shutil.disk_usage('/tmp').free < 512*1024**2:
    raise RuntimeError('Reserve')
state=json.loads((PRIVATE/'state.json').read_text())
inputs=json.loads((PRIVATE/'inputs.json').read_text())
if state['status']!='PASS' or len(state['completed'])!=4:
    raise RuntimeError('Incomplete final run')
for p in inputs['pins']:
    check(p)
for e in state['completed']:
    for key in ('source','snapshot','object','log','timing'):
        check(e[key])
    if e['exit_code']!=0 or Path(e['object']['path']).is_symlink():
        raise RuntimeError('Not a fresh regular PASS output')
BUNDLE.mkdir()
artifacts=[]

def copy(src, rel):
    dst=BUNDLE/rel
    dst.parent.mkdir(parents=True,exist_ok=True)
    data=Path(src).read_bytes()
    dst.write_bytes(data)
    if dst.read_bytes()!=data:
        raise RuntimeError('Copy mismatch')
    artifacts.append(record(dst))

copy(DRIVER,'driver.py')
copy(__file__,'freeze-evidence.py')
copy(DC/'research/adaptive-power-recovery2011-proposal.md','proposal.md')
copy(DC/'research/adaptive-power-recovery2011-cache-audit.json','cache-audit.json')
attempts=[]
paths=Path('/tmp/native-adaptive-power-attempts').read_text().splitlines()
if len(paths)!=3 or paths[-1]!=str(PRIVATE):
    raise RuntimeError('Unexpected attempts inventory')
for i,p in enumerate(paths,1):
    p=Path(p)
    s=json.loads((p/'state.json').read_text())
    copy(p/'state.json',f'attempt-{i}/state.json')
    copy(p/'inputs.json',f'attempt-{i}/inputs.json')
    for f in sorted((p/'logs').iterdir()):
        if f.is_file(): copy(f,f'attempt-{i}/logs/{f.name}')
    attempts.append(dict(private=str(p),state=record(p/'state.json'),status=s['status'],
                         failure=s.get('failure'),completed=s['completed']))
packet=dict(
    format='adaptive-power-recovery-private-replay-v1',status='PASS',
    scope='Four new leaves only. Same actual literal tuple gives 2n=R+1, 4XY²|v, q²Y|v, q|3X, H|3(X−2^R), and X=2^R. No source/index/parity/q|X/X>=2/power premise. Mersenne exclusion and canonical converse remain separate.',
    private=str(PRIVATE),driver=record(DRIVER),inputs_record=record(PRIVATE/'inputs.json'),
    state_record=record(PRIVATE/'state.json'),inputs=inputs,completed=state['completed'],
    attempts=attempts,artifact_texts=artifacts,final_free_bytes=shutil.disk_usage('/tmp').free,
    corrections=[
        'Attempt1: nested by positivity; omega proof scope in a theorem statement. No mathematical premise changed.',
        'Attempt2: Projection pair PASS; Recovery needed explicit Nat/Int casts, dependent Pell-base simp congruence, exponent normalization, dvd_abs arguments, local positive-Q fact, and narrowing a broad nlinarith call. The terminal heartbeat failure and all earlier diagnostics are preserved.',
        'Attempt3: all four leaves clean PASS;14 standard axiom reports. No source changes after this run.'
    ],
    provider_note='Original frozen Strong author provider is retained. Root separately reported byte-identical independent acceptance. Recovery imports this same-run freshly author-validated Projection object, not a preaccepted cache module. No dependency or Foundation rebuild.',
)
PACKET.write_text(json.dumps(packet,indent=2)+'\n')
MANIFEST.write_text(json.dumps(dict(format='replay-text-manifest-v1',files=artifacts+[record(PACKET)]),indent=2)+'\n')
print(json.dumps(dict(packet=record(PACKET),manifest=record(MANIFEST),driver=record(DRIVER),
                     files=len(artifacts),attempts=len(attempts),sources=inputs['sources'],
                     free_bytes=shutil.disk_usage('/tmp').free),indent=2))
