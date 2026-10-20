#!/usr/bin/env python3
from pathlib import Path
import argparse,importlib.util,json
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
f=Path(__file__).resolve().parent.parent/'research/theory218/uniform_rho8_obstruction.py'
s=importlib.util.spec_from_file_location('obstruction',f);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
r=m.verify();a.output.write_text(json.dumps(r,indent=2)+'\n');print(r['status'])
