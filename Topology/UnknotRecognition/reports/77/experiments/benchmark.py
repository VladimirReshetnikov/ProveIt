"""Paired local-kernel timings; not whole-recognizer performance claims."""
from __future__ import annotations
import csv
import json
from pathlib import Path
import platform
import statistics
import time
from boundary_kernel.kernel import Builder,Kernel,certificate
from boundary_kernel.binary import magnus
from boundary_kernel.verify import verify_certificate


def family(k,g=3):
    b=Builder(); u=b.word([1,4,2,-3]); power=b.add('pow',u,'0b1'+'0'*k)
    c=b.word([1,2,-1,-2]); root=b.cat(b.cat(power,c),b.inv(power))
    return b.build(root)


def median_call(f,repeats=7):
    values=[]
    for _ in range(repeats):
        start=time.perf_counter(); f(); values.append(time.perf_counter()-start)
    return statistics.median(values)


def run(output_dir):
    output=Path(output_dir); output.mkdir(exist_ok=True,parents=True)
    rows=[]
    for k in (0,4,8,12,15,64,256,1024,4096,16384):
        s=family(k); kernel=Kernel(3)
        compressed=median_call(lambda:s.evaluate(kernel))
        literal=None
        if k<=15:
            w=s.expand(300000)
            assert kernel.literal(w)==s.evaluate(kernel)
            literal=median_call(lambda:kernel.literal(w),3)
        cert=certificate(s,3)
        assert verify_certificate(cert)
        rows.append(dict(power_bit_index=k,slp_rules=len(s.rules),
                         encoded_bytes=len(json.dumps(s.payload()).encode()),
                         expanded_length=('8*2^%d+4'%k),
                         scalar_seconds=compressed,literal_seconds=literal,
                         literal_over_scalar=None if literal is None else literal/compressed,
                         independent_certificate_valid=True))
    fields=list(rows[0])
    with (output/'compression.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields); writer.writeheader(); writer.writerows(rows)
    genus_rows=[]
    for g in (2,4,8,16,32,64):
        b=Builder(); a=b.word([x for i in range(g) for x in (2*i+1,2*i+2,-2*i-1,-2*i-2)])
        a=b.add('pow',a,'0b1'+'0'*256); s=b.build(a)
        k=Kernel(g)
        scalar=median_call(lambda:s.evaluate(k),5)
        quadratic=median_call(lambda:magnus(s,g),5)
        genus_rows.append(dict(genus=g,slp_rules=len(s.rules),scalar_seconds=scalar,
                               binary_magnus_seconds=quadratic,
                               binary_over_scalar=quadratic/scalar))
    with (output/'genus_scaling.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(genus_rows[0])); writer.writeheader();writer.writerows(genus_rows)
    data=dict(python=platform.python_version(),implementation=platform.python_implementation(),
              platform=platform.platform(),processor=platform.processor(),
              timer='time.perf_counter; medians; no process isolation',
              scalar_repeats=7,literal_repeats=3,genus_repeats=5,
              scope='SLP evaluation only, excludes input parsing/source geometry/native recognition',
              compression=rows,genus_scaling=genus_rows)
    (output/'benchmark.json').write_text(json.dumps(data,indent=2)+'\n')
    return data


if __name__ == '__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output-dir',default='results')
    args=p.parse_args();print(json.dumps(run(args.output_dir),indent=2))
