#!/usr/bin/env python3
"""Optional bounded search replay, with logs isolated under the output directory."""
from pathlib import Path
import argparse,gzip,hashlib,json,shutil,subprocess,tempfile
HERE=Path(__file__).resolve().parent
NAMES={'exact_pair':'resource_merge_search.cpp','semantic_pair':'semantic_merge_search.cpp','single_entry_splice':'edge_splice_search.cpp','multi_entry_splice':'multi_entry_splice_search.cpp'}
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);p.add_argument('--which',nargs='+',choices=list(NAMES),default=list(NAMES));a=p.parse_args()
assert __debug__;a.output.mkdir(parents=True,exist_ok=True)
raw=(HERE/'search/cases.txt.gz').read_bytes();assert hashlib.sha256(raw).hexdigest()=='3ebf4ea86da4a6bcd12b857cb67b3ba6b32e597b94eb8bfeef5e3ff03cddf31d'
fixture=gzip.decompress(raw);assert hashlib.sha256(fixture).hexdigest()=='71fd6d7d0460c3f920ba945c04f2e3a1b571ce070e445ae019417ff0d675abc1'
compiler=shutil.which('g++') or shutil.which('clang++');assert compiler,'C++17 compiler required'
with tempfile.TemporaryDirectory(prefix='zfc-interpreter-search-') as tmp:
    tmp=Path(tmp);cases=tmp/'cases.txt';cases.write_bytes(fixture)
    for name in a.which:
        out=(a.output/name).resolve();out.mkdir(parents=True,exist_ok=True);exe=tmp/name
        subprocess.run([compiler,'-O3','-std=c++17',str(HERE/'search'/NAMES[name]),'-o',str(exe)],check=True)
        with (out/'run.log').open('w') as log:subprocess.run([str(exe),str(cases)],cwd=out,stdout=log,stderr=subprocess.STDOUT,check=True)
        summary=json.loads((out/'merge-search-summary.json').read_text());assert summary['full_literal_pass_count']==0
        assert summary['instruction_cases']==8385 and summary['baseline_pairs_exercised']==490
        print(name,json.dumps(summary),flush=True)
