"""Reproduce the selected result and all transparent comparison controls."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(relative, *args):
    subprocess.run([sys.executable, str(ROOT / relative), *args],
                   cwd=ROOT, check=True)


if __name__ == '__main__':
    run('code/horn/test_horn.py')
    run('code/ranked/test_ranked.py')
    run('code/ranked/test_recursive_arity.py')
    run('code/ranked/test_five_control.py')
    run('code/packet/test_packets.py')
    run('measure.py')
    run('build_report.py', *(['--pdf'] if '--pdf' in sys.argv else []))
    print('Reproduction completed without failures.')
