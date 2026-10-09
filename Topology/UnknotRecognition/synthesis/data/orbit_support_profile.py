"""Reproduce merger-call categories on the raw 16-crossing circle query."""
import json
from collections import Counter
from pathlib import Path
import sys
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot import Diagram
from fastunknot.interval_orbits import count_orbits
from fastunknot.normal_seed import normal_seed_decide
from normal_orbit_research.supports import baseline, pins, BASELINE
from normal_orbit_research.seeds import digest

before = pins()
records = []
old, old_hash = baseline()
for label, counter in [('old', old), ('new', count_orbits)]:
    categories, orbit_stats = Counter(), []
    merger = counter.__globals__['periodic_merge']
    def tracked_merge(a, b, **options):
        overlap = min(a.d, b.d)-max(a.a, b.a)+1
        categories['disjoint' if overlap <= 0 else 'overlapping'] += 1
        return merger(a, b, **options)
    def tracked_count(*args, **options):
        result = counter(*args, **options)
        orbit_stats.append(result.stats)
        return result
    with patch.dict(counter.__globals__, periodic_merge=tracked_merge), \
         patch('fastunknot.weighted_orbits.count_orbits', tracked_count):
        result = normal_seed_decide(Diagram.from_braid(17, list(range(1, 17))))
    assert result['status'] == 'UNKNOT'
    records.append(dict(engine=label, categories=dict(categories), orbit_stats=orbit_stats,
                        work=result['work'], certificate_sha256=digest(result['certificate'])))
assert records[0]['certificate_sha256'] == records[1]['certificate_sha256']
assert pins() == before
Path(__file__).with_name('orbit-support-profile.json').write_text(json.dumps(
    dict(baseline_commit=BASELINE, baseline_module_sha256=old_hash,
         source_sha256=before, records=records), indent=2)+'\n')
for row in records:
    print(row['engine'], row['categories'], row['work'])
