"""Usage: python -m boundary_kernel word.json --genus 3 [--safe] [--verify]."""
import argparse
import json
import sys
from .kernel import SLP, certificate
from .verify import verify_certificate


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input')
    p.add_argument('--genus',type=int)
    p.add_argument('--safe',action='store_true')
    p.add_argument('--verify',action='store_true')
    args = p.parse_args()
    try:
        with open(args.input,encoding='utf-8') as f: data = json.load(f)
        if args.verify:
            ok = verify_certificate(data)
            print(json.dumps({'algebraic_certificate_valid':ok,'source_geometry_verified':False}))
            return 0 if ok else 1
        if args.genus is None: p.error('--genus is required for evaluation')
        result = certificate(SLP(data['rules'],data.get('root')),args.genus,args.safe)
        print(json.dumps(result,indent=2))
        return 0
    except (OSError, ValueError, TypeError, KeyError) as e:
        print(str(e),file=sys.stderr)
        return 2


if __name__ == '__main__': raise SystemExit(main())
