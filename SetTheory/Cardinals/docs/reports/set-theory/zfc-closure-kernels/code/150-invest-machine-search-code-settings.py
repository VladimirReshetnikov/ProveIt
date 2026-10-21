"""Shared portable arguments for the exploratory Python searches."""
from pathlib import Path
import argparse,sys
p=argparse.ArgumentParser(add_help=False);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
a,left=p.parse_known_args();sys.argv=[sys.argv[0],*left]
Z=a.repo.resolve()
if not(Z/'candidate-k218/k218.native.tm').is_file():Z=Z/'Computability/BusyBeaver/Research/ZFC'
if not(Z/'candidate-k218/k218.native.tm').is_file():raise ValueError('--repo must name ProveIt or the ZFC research directory')
OUT=a.output.resolve()
if OUT.exists():raise ValueError('--output must be a fresh directory')
OUT.mkdir(parents=True)
