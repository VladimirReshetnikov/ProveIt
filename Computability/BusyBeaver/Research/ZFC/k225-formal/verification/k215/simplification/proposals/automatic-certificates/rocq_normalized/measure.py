#!/usr/bin/env python3
"""Measure one child command in a fresh process; Linux RSS is reported in KiB."""
import json, resource, subprocess, sys, time
from pathlib import Path
start=time.monotonic()
p=subprocess.run(sys.argv[2:])
r=resource.getrusage(resource.RUSAGE_CHILDREN)
Path(sys.argv[1]).write_text(json.dumps(dict(elapsed=time.monotonic()-start,
    user=r.ru_utime,system=r.ru_stime,max_rss_kib=r.ru_maxrss,exit_code=p.returncode),indent=2)+'\n')
raise SystemExit(p.returncode)
