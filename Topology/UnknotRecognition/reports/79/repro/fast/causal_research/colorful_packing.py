"""Exact packing of supplied local-trace items under one supplied coloring.

This module implements only the finite color-mask dynamic program.  It does
not construct a perfect hash family or authenticate geometric trace items.
In particular, a negative answer for one coloring is not a complete negative
answer to the uncolored packing or Pachner descent problem.
"""


def _nonnegative_integer(value, label):
    if type(value) is not int or value < 0:
        raise ValueError(f'{label} must be a nonnegative integer')


def pack_colorful_candidates(candidates, coloring, *, max_upward, goal):
    """Maximize capped loss from mask-disjoint items within the upward budget.

    ``candidates`` is a list of dictionaries containing ``footprint`` (a
    nonempty list of distinct original source IDs), ``upward`` (a
    nonnegative integer), and ``loss`` (a positive integer).  Additional
    fields, such as a trace certificate, are ignored and left untouched.
    Source IDs index the supplied list ``coloring`` of nonnegative integer
    color labels.  Items with an internal color collision are discarded.

    The objective is maximum ``min(goal, total loss)``, then minimum total
    upward count.  Remaining ties are broken deterministically, without a
    global cardinality or lexicographic optimality claim.  Selected indices
    always refer to the original input list, including when preceding items
    were discarded.

    The result includes both the actual and capped loss, the exact union of
    source footprints, and the selected colors.  For ``color_mask``, bit i
    denotes ``color_labels[i]``; unused numeric gaps between labels have no
    effect on the algorithm or its resource use.  Neither the inputs nor
    candidate payloads are modified.  All input is validated even for a
    zero goal; a zero goal returns the empty packing.

    For M items and q distinct supplied colors, the dynamic program has at
    most 2**q * (max_upward + 1) states.  It uses a separate previous-state
    table for every item, so a zero-cost item cannot be selected twice.
    Stored witness tuples are immutable and have at most q entries.
    """
    _nonnegative_integer(max_upward, 'max_upward')
    _nonnegative_integer(goal, 'goal')
    if type(candidates) is not list:
        raise ValueError('candidates must be a list')
    if type(coloring) is not list:
        raise ValueError('coloring must be a list')
    for index, color in enumerate(coloring):
        _nonnegative_integer(color, f'coloring[{index}]')

    color_labels = sorted(set(coloring))
    color_bits = {color: 1 << index
                  for index, color in enumerate(color_labels)}
    items = []
    normalized = []
    noncolorful = []
    over_budget = []
    for index, candidate in enumerate(candidates):
        if (type(candidate) is not dict
                or not {'footprint', 'upward', 'loss'} <= set(candidate)):
            raise ValueError(f'candidate {index} requires footprint, upward and loss')
        footprint = candidate['footprint']
        if type(footprint) is not list or not footprint:
            raise ValueError(f'candidate {index} footprint must be a nonempty list')
        if any(type(source) is not int or not 0 <= source < len(coloring)
               for source in footprint):
            raise ValueError(f'candidate {index} has an invalid source ID')
        if len(set(footprint)) != len(footprint):
            raise ValueError(f'candidate {index} repeats a source ID')
        upward, loss = candidate['upward'], candidate['loss']
        _nonnegative_integer(upward, f'candidate {index} upward')
        if type(loss) is not int or loss <= 0:
            raise ValueError(f'candidate {index} loss must be a positive integer')
        sources = tuple(sorted(footprint))
        normalized.append((sources, upward, loss))
        colors = {coloring[source] for source in sources}
        if len(colors) != len(sources):
            noncolorful.append(index)
            continue
        if upward > max_upward:
            over_budget.append(index)
            continue
        mask = sum(color_bits[color] for color in colors)
        items.append((index, mask, upward, min(goal, loss)))

    # (mask, upward) -> (capped loss, immutable original-index witness).
    states = {(0, 0): (0, ())}
    peak_states, transitions = 1, 0
    for index, item_mask, upward, loss in items:
        following = states.copy()
        for (mask, used), (profit, witness) in states.items():
            if mask & item_mask or used + upward > max_upward:
                continue
            transitions += 1
            key = (mask | item_mask, used + upward)
            proposed = (min(goal, profit + loss), witness + (index,))
            previous = following.get(key)
            if (previous is None or proposed[0] > previous[0]
                    or (proposed[0] == previous[0]
                        and (len(proposed[1]), proposed[1])
                        < (len(previous[1]), previous[1]))):
                following[key] = proposed
        states = following
        peak_states = max(peak_states, len(states))

    (mask, upward), (capped_loss, selected) = min(
        states.items(), key=lambda item: (
            -item[1][0], item[0][1], len(item[1][1]), item[1][1]))
    footprint = sorted({source for index in selected
                        for source in normalized[index][0]})
    actual_loss = sum(normalized[index][2] for index in selected)
    return dict(selected_indices=list(selected), upward=upward,
                actual_loss=actual_loss, capped_loss=capped_loss,
                goal_reached=(capped_loss == goal), footprint=footprint,
                colors=sorted({coloring[source] for source in footprint}),
                color_mask=mask, color_labels=color_labels,
                discarded_noncolorful=noncolorful,
                discarded_over_budget=over_budget,
                stats=dict(input_items=len(candidates), eligible_items=len(items),
                           peak_states=peak_states, transitions=transitions))
