"""A bounded universal-source candidate/scheduler check, with no eager F loop."""
from hashlib import sha256
import gzip
import json
from pathlib import Path
import scheduler_reference as s

HERE = Path(__file__).resolve().parent
SOURCE_SHA = 'fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'
SOURCE_BYTES = 32034272


def require(ok, detail):
    if not ok:
        raise ValueError(detail)


def main():
    with gzip.open(HERE / 'source.json.gz', 'rb') as stream:
        raw = stream.read(SOURCE_BYTES + 1)
    require(len(raw) == SOURCE_BYTES and sha256(raw).hexdigest() == SOURCE_SHA, 'universal source bytes')
    data = json.loads(raw)
    del raw
    a = s.lazy.compile_lazy_source(data)
    del data
    require((a.m, a.p, a.a, a.J, a.factors) == (122622, 66066, 75495, 0, 269291358255), 'universal ledger')
    delta = max([0] + [len(v) for v in a.home_out.values()] + [len(v) for v in a.home_in.values()])
    require(delta == 2, 'universal Delta')
    x = a.encode('START', 1, 0)
    require(sorted(x) == [-20380381, 0, 1019018, 1019019, 20380380], 'universal initial support')
    targets = ['h0000B0T1', 'p00001R0T1', 'p00001R0T2']
    initial = x
    total_k = 0
    counts = []
    for q in targets:
        slots = s.slots(a, x)
        require(len(slots) == 170, 'universal n=5 candidate slot count')
        enabled = {i for on, i in slots if on}
        require(enabled == set(a.candidate_indices(x)), 'universal candidate set')
        y, stats = a.step(x, verify=True, trace=True)
        require(y == a.encode(q, 1, 0), 'universal startup target')
        k = stats['changed_factors']
        ok, z, records = s.run(a, x, 1, k)
        require(ok and z == y, 'universal scheduler step')
        total_k += k
        counts.append(dict(candidate_slots=len(slots), enabled_distinct=len(enabled), changed_factors=k))
        x = y
    ok, y, records = s.run(a, initial, 3, total_k + 2)
    require(ok and y == x, 'universal total-budget scheduler')
    require(sum(r['kind'] == 'complete' for r in records) == 3, 'universal completion rounds')
    require(sum(r['kind'] == 'change' for r in records) == total_k, 'universal total event count')
    require(all(r['kind'] == 'idle' for r in records[3 + total_k:]), 'universal idle padding')
    if total_k:
        ok, _, _ = s.run(a, initial, 3, total_k - 1)
        require(not ok, 'universal underbudget rejection')
    result = dict(status='passed', source_sha256=SOURCE_SHA, ledger=a.ledger(), Delta=delta,
                  n5_candidate_slots=170, startup_steps=3, total_changing_factors=total_k,
                  counts=counts, note='Finite general-scheduler check; no general quartic exporter is implemented.')
    (HERE / 'universal-slots-receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
