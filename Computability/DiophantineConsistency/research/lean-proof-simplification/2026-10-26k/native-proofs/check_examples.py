"""Replay the two standalone Lean checks; does not claim full project validation."""
from pathlib import Path
import hashlib, json, subprocess, time, sys

HERE = Path(__file__).resolve().parent
env_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE.parents[1] / 'lean-env/validation'
lake = Path(sys.argv[2]) if len(sys.argv) > 2 else HERE.parents[1] / 'lean-env/lean-4.32.0-linux/bin/lake'
out = HERE / 'validation'
out.mkdir(exist_ok=True)
records = []
for name in ['SignedModEq.lean', 'OneHotSupport.lean']:
    path = HERE / name
    command = [str(lake), 'env', 'lean', str(path)]
    start = time.time()
    result = subprocess.run(command, cwd=env_dir, capture_output=True, text=True)
    (out / (path.stem + '.log')).write_text(result.stdout + result.stderr)
    records.append({'source': name, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'command': command, 'cwd': str(env_dir), 'returncode': result.returncode,
        'elapsed_seconds': round(time.time()-start, 3),
        'status': 'kernel_checked' if result.returncode == 0 else 'failed',
        'scope': 'standalone helper, not full modified repository module'})
    print(name, result.returncode)
(out / 'results.json').write_text(json.dumps(records, indent=2) + '\n')
sys.exit(any(record['returncode'] != 0 for record in records))
