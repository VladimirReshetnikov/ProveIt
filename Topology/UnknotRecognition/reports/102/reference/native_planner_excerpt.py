"""Transcribed native planner functions for an explicit algorithm comparison.

Source: ProveIt, Topology/UnknotRecognition/fast/fastunknot/core_handlebody.py
revision 8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4,
Git blob 13935f9cfa9ecf70fa5966a2ceec58f0f3167ff7.
Only these two function bodies and their required import are reproduced.
The containing file is NOT a byte-identical full source snapshot. Source MIT-0.
"""
from heapq import heappop, heappush


def capped_cancellation_plan(counts, *, check=lambda: None):
    rows = {}
    for r, values in counts.items():
        check()
        if type(r) is not int or r < 0 or type(values) is not dict:
            raise ValueError('invalid occurrence row')
        row = {}
        for c, value in values.items():
            if type(c) is not int or c < 0 or type(value) is not int or value < 0:
                raise ValueError('invalid occurrence entry')
            if value:
                row[c] = min(2, value)
        rows[r] = row
    schedule, updates, scans = [], 0, 0
    while rows:
        check()
        totals = {}
        for row in rows.values():
            for c, value in row.items():
                totals[c] = totals.get(c, 0) + value
                scans += 1
        candidates = []
        for r, row in rows.items():
            size = sum(row.values())
            for c, value in row.items():
                scans += 1
                if value == 1:
                    candidates.append(((size - 1) * (totals[c] - 1), size, r, c))
        if not candidates:
            break
        _, _, r, c = min(candidates)
        donor = rows.pop(r)
        donor.pop(c)
        for row in rows.values():
            check()
            multiplicity = row.pop(c, 0)
            if multiplicity:
                for h, value in donor.items():
                    row[h] = min(2, row.get(h, 0) + multiplicity * value)
                    updates += 1
        schedule.append([r, c])
    return dict(cancellations=schedule, remaining_rows=sorted(rows),
                stats=dict(entry_scans=scans, entry_updates=updates))


def leaf_cancellation_plan(counts, *, check=lambda: None):
    rows = {r: {c: min(2, v) for c, v in values.items() if v}
            for r, values in counts.items()}
    incident = {}
    for r, row in rows.items():
        for c in row:
            incident.setdefault(c, []).append(r)
    queue = []
    for r, row in rows.items():
        if len(row) == 1 and next(iter(row.values())) == 1:
            heappush(queue, r)
    schedule, visits = [], 0
    while queue:
        check()
        r = heappop(queue)
        if r not in rows:
            continue
        row = rows[r]
        if len(row) != 1 or next(iter(row.values())) != 1:
            continue
        rows.pop(r)
        c = next(iter(row))
        schedule.append([r, c])
        for i in incident[c]:
            check()
            visits += 1
            if i in rows:
                rows[i].pop(c, None)
                if len(rows[i]) == 1 and next(iter(rows[i].values())) == 1:
                    heappush(queue, i)
    return dict(cancellations=schedule, remaining_rows=sorted(rows),
                stats=dict(incidence_visits=visits))
