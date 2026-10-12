"""Independent all-primal-forests raw stopping-set check, conditional on core charts."""


def verify_all_forest_obstruction(core, row_ids, *, check=lambda: None):
    check()
    if type(row_ids) is not list or not row_ids:
        return False
    seen, totals = set(), {}
    for r in row_ids:
        check()
        if type(r) is not int or r < 0 or r >= len(core['handles2']) or r in seen:
            return False
        seen.add(r)
        row = core['handles2'][r]
        if row['id'] != r:
            return False
        for flag in row['cycle']:
            check()
            if flag['dimension'] == 1:
                e = flag['handle']
                if type(e) is not int or e < 0 or e >= len(core['handles1']):
                    return False
                totals[e] = min(2, totals.get(e, 0) + 1)
    return all(value == 2 for value in totals.values())
