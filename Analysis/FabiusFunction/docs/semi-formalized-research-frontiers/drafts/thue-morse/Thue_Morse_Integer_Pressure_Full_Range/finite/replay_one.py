"""Regenerate one pressure trace, match its state hashes, and independently audit it.

The producer and independent verifier must first be compiled as in README.md.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,sys
sys.set_int_max_str_digits(0)
root=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('m',type=int);p.add_argument('--output',type=Path,default=root/'generated')
p.add_argument('--producer',type=Path,default=root/'produce');p.add_argument('--auditor',type=Path,default=root/'audit')
p.add_argument('--reuse',action='store_true',help='Reuse a local trace, but still check all state hashes and audit it')
args=p.parse_args();assert 2<=args.m<=111
args.output.mkdir(parents=True,exist_ok=True)
output=args.output/f'interval_m{args.m:03}.json';trace=Path(str(output)+'.trace.gz')
if not(args.reuse and output.exists() and trace.exists()):
    subprocess.run([str(args.producer.resolve()),str(args.m),'256',str(output.resolve())],check=True)
index=json.loads((root/'state_indices'/f'compact_m{args.m:03}.json').read_text())
with gzip.open(trace,'rb')as f:
    header=[f.readline().decode().strip()for _ in range(3)]
    assert header==[index['header'],index['scale'],index['parity_norm_fractions']]
    count=0
    for n,line in enumerate(f):
        fields=line.split();assert len(fields)==args.m+4 and int(fields[0])==n
        assert index['orders'][n]==dict(order=n,state_sha256=hashlib.sha256(b' '.join(fields)).hexdigest())
        count+=1
assert count==6*args.m-1
pressure=json.loads(output.read_text());rows=pressure['pressure_bounds']
assert [r['degree']for r in rows]==list(range(2*args.m,6*args.m,2))
for i,r in enumerate(rows):
    lo,hi,den=map(int,(r['lower_numerator'],r['upper_numerator'],r['denominator']))
    assert den>0 and lo<=hi and ((lo>0) if i else (lo<=0<=hi))
audit_output=args.output/f'independent_m{args.m:03}.json'
subprocess.run([str(args.auditor.resolve()),str(trace.resolve()),str(audit_output.resolve())],check=True)
fresh=json.loads(audit_output.read_text())
reference=json.loads((root/'independent_numeric_index.json').read_text())['cases'][args.m-2]
assert reference['m']==args.m
canonical=json.dumps(fresh['pressure_bounds'],sort_keys=True,separators=(',',':')).encode()
assert hashlib.sha256(canonical).hexdigest()==reference['pressure_bounds_canonical_sha256']
assert hashlib.sha256(Path(str(audit_output)+'.radii.gz').read_bytes()).hexdigest()==reference['fresh_radii_sha256']
print(f'm={args.m}: all {count} states match; both exact pressure enclosures pass.')
