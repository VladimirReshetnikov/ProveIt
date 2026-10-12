"""A checkpoint-bounded restart race between two certified AHT sweeps.

The initial allowance is 8*(k+1)*(bit_length(n)+1). Both directions get the
same allowance per round, then it doubles. The wider-end rule chooses order
only. An exhaustion callback counts as work. With no cycle cap, if W is the
smaller complete checkpoint count and L is the initial allowance, total
attempt checkpoints are at most 12*max(L,W). This is a checkpoint bound, not
a constant-factor wall-clock or bit-cost comparison. Each between-checkpoint
block still has the old polynomial input-size bound.
"""
from .interval_orbits import OrbitResult, _count_orbits, _validate, _wide_end_is_left


def race_orbits(n, pairings, *, max_cycles=None, periodic_rule='fine_wilf',
                check=None, record_certificate=False, merger_scheduler='adaptive'):
    outer_check = check if check is not None else lambda: None
    startup = 0

    def startup_check():
        nonlocal startup
        outer_check()
        startup += 1

    startup_check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if not isinstance(merger_scheduler,str) or merger_scheduler not in ('adaptive','legacy','queue'):
        raise ValueError("merger_scheduler must be 'adaptive', 'legacy' or 'queue'")
    pairs = _validate(n,pairings,max_cycles,periodic_rule)
    prefer_reverse = _wide_end_is_left(pairs,startup_check)
    order = (1,0) if prefer_reverse else (0,1)
    initial = allowance = 8*(len(pairs)+1)*(n.bit_length()+1)
    attempts = exhausted = rounds = cycles = work = 0
    direction_work = [0,0]
    direction_cycles = [0,0]
    current_stats = None

    # A fresh local exception prevents a caller's unrelated exception from
    # being mistaken for ordinary budget exhaustion.
    class WorkLimit(Exception):
        pass

    def finish(result, winner, winning_work):
        stats = dict(result.stats)
        stats.update(race_attempts=attempts,race_restarts=attempts-1,race_work_exhaustions=exhausted,
            race_rounds=rounds,race_checkpoint_work=work,race_startup_work=startup,
            race_initial_allowance=initial,race_final_allowance=allowance,
            race_winning_direction=winner,race_winning_work=winning_work,
            race_winning_cycles=result.cycles if result.complete else 0,
            race_forward_work=direction_work[0],race_reverse_work=direction_work[1],
            race_forward_cycles=direction_cycles[0],race_reverse_cycles=direction_cycles[1])
        return OrbitResult(result.complete,result.orbits,cycles,stats,result.certificate)

    while True:
        rounds += 1
        for direction in order:
            attempts += 1
            used = 0
            current_stats = None

            def limited_check():
                nonlocal used, work
                outer_check()
                used += 1
                work += 1
                direction_work[direction] += 1
                if used > allowance:
                    raise WorkLimit()

            def cycle_started(stats):
                nonlocal cycles, current_stats
                cycles += 1
                direction_cycles[direction] += 1
                current_stats = stats

            remaining = None if max_cycles is None else max_cycles-cycles
            try:
                answer = _count_orbits(n,pairs,max_cycles=remaining,periodic_rule=periodic_rule,
                    check=limited_check,record_certificate=record_certificate,
                    merger_scheduler=merger_scheduler,sweep_direction=('reverse' if direction else 'forward'),
                    _cycle_started=cycle_started)
            except WorkLimit:
                exhausted += 1
                if max_cycles is not None and cycles == max_cycles:
                    assert current_stats is not None
                    partial = OrbitResult(False,None,0,current_stats)
                    return finish(partial,-1,0)
                continue
            return finish(answer,direction if answer.complete else -1,used if answer.complete else 0)
        allowance *= 2
