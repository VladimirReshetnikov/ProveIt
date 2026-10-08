#!/usr/bin/env python3
from pathlib import Path
import sys,json,argparse
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from terminal_updates.terminal import verify_exact_certificate

def main():
    parser=argparse.ArgumentParser(description='Check a signed terminal cofactor certificate; does not verify knot geometry.')
    parser.add_argument('certificate',type=Path);args=parser.parse_args()
    try:
        certificate=json.loads(args.certificate.read_text())
        valid=verify_exact_certificate(certificate)
    except (ValueError,TypeError,KeyError,OSError) as exc:
        print(f'INVALID: {exc}',file=sys.stderr);return 1
    print('VALID algebraic cofactor certificate' if valid else 'INVALID certificate')
    return 0 if valid else 1
if __name__=='__main__':raise SystemExit(main())
