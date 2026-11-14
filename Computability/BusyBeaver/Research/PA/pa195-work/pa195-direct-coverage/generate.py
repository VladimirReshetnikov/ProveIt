#!/usr/bin/env python3
"""Generate closed Lean checks for ordinal ranges of the formal source tree."""
import argparse
from pathlib import Path

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', type=Path, required=True)
p.add_argument('--start-site', type=int, default=0)
p.add_argument('--stop-site', type=int, default=3700)
p.add_argument('--batch-size', type=int, default=10)
a = p.parse_args()
if not (0 <= a.start_site <= a.stop_site <= 3700 and a.batch_size > 0):
    raise SystemExit('invalid source-site range or batch size')
a.out.mkdir(parents=True, exist_ok=True)
for first in range(a.start_site, a.stop_site, a.batch_size):
    last = min(first + a.batch_size, a.stop_site)
    module = f'PA195DirectBatch{first:04d}_{last:04d}'
    source = f'''import PA195SourcePhysical
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {module}
open PA195SourcePhysical

theorem verified : (List.range\' {first} {last - first}).all acceptedSite = true := by decide +kernel
#print axioms verified
end {module}
'''
    (a.out / f'{module}.lean').write_text(source)
print(f'Generated {(a.stop_site - a.start_site + a.batch_size - 1) // a.batch_size} Lean batches, formal source sites {a.start_site}..{a.stop_site - 1}')
