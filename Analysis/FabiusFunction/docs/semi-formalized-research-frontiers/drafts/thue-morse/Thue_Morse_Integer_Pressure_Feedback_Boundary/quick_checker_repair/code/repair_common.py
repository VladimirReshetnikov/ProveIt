"""Fail-closed helpers for the independently packaged quick-checker repair."""
from pathlib import Path
import argparse

class VerificationError(RuntimeError):
    pass

def require(condition, message):
    if not condition:
        raise VerificationError(message)

def options(description):
    root=Path(__file__).resolve().parents[1]
    p=argparse.ArgumentParser(description=description)
    p.add_argument('--data-dir',type=Path,default=root/'data',help='Original report data directory, read-only')
    p.add_argument('--output-dir',type=Path,default=root/'results',help='Write new audit records here, never into original data')
    args=p.parse_args()
    require(args.output_dir.resolve() != args.data_dir.resolve() and args.data_dir.resolve() not in args.output_dir.resolve().parents,
            "Output directory must be outside the original data directory")
    args.output_dir.mkdir(parents=True,exist_ok=True)
    return args
