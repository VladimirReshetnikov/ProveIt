"""Run the predeclared comparison and retain its shared-host environment.

This runner performs exactly the benchmark's fifty calls. The preceding audit
must already exist and pass the benchmark's independent replay. CPU affinity
does not reserve a core or suppress unrelated jobs.
"""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import subprocess
import sys


DATA = Path(__file__).resolve().parent
FAST = DATA.parent.parent/'fast'


def snapshot():
    rows = subprocess.check_output(
        ['ps', '-eo', 'pid,psr,pcpu,comm', '--sort=-pcpu'], text=True)
    return dict(utc=datetime.now(timezone.utc).isoformat(),
                processes=rows.splitlines()[:12])


def main():
    assert __debug__
    assert 5 in os.sched_getaffinity(0)
    os.sched_setaffinity(0, {5})
    command = [sys.executable, '-B', '-S', '-m',
               'pachner_descent_research.benchmark',
               '--audit', '../synthesis/data/pachner-descent-audit.json',
               '--output', '../synthesis/data/pachner-descent-benchmark.json']
    environment = dict(affinity=sorted(os.sched_getaffinity(0)),
        host_logical_cpus=os.cpu_count(), platform=platform.platform(),
        python=sys.version, command=command,
        controls='No competing heavy jobs from this task. Unrelated repository '
                 'Lean or research jobs may remain active. CPU5 affinity is '
                 'not an exclusive reservation.', before=snapshot())
    output = DATA/'pachner-descent-environment.json'
    output.write_text(json.dumps(environment, indent=2)+'\n')
    with (DATA/'pachner-descent-benchmark.txt').open('w') as log:
        result = subprocess.run(command, cwd=FAST, stdout=log,
                                stderr=subprocess.STDOUT,
                                env=dict(os.environ, PYTHONPATH='.'))
    environment.update(after=snapshot(), returncode=result.returncode)
    output.write_text(json.dumps(environment, indent=2)+'\n')
    print(json.dumps(dict(returncode=result.returncode,
                          log=str(log.name), environment=str(output))))
    sys.exit(result.returncode)


if __name__ == '__main__':
    main()
