"""Verify the delivered SHA-256 inventory before regenerating receipts."""
from pathlib import Path
import hashlib,sys
ROOT=Path(__file__).resolve().parents[1]

def main():
    lines=(ROOT/'MANIFEST.sha256').read_text().splitlines()
    count=0;bad=[]
    for row in lines:
        if not row or row.startswith('#'):continue
        digest,name=row.split('  ',1)
        p=ROOT/name
        if p.is_absolute() and not p.resolve().is_relative_to(ROOT.resolve()):
            raise ValueError('manifest path outside package')
        if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
            bad.append(name)
        count+=1
    if bad:
        for name in bad:print('MISMATCH',name)
        raise SystemExit(1)
    print(f'All {count} manifest entries match SHA-256.')
if __name__=='__main__':main()
