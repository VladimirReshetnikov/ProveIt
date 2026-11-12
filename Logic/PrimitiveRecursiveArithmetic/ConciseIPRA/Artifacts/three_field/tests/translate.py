"""Untrusted, execution-guided producers for the three-field protocol.

Every result must be checked by the standalone acceptance modules. The
canonical compiler rejects encounters outside its stated meaningful-formula
proof fragment; it is not claimed to preserve every raw certificate.
"""
import copy


def to_four_fields(data):
    """Expand triple packets; leave the final public goal unchanged.

    A certificate may have unused prefix data. Only well-formed triple
    entries are expanded here; a successful three-field execution consumes
    only such entries, so all consumed positions receive the required map.
    """
    out = copy.deepcopy(data)
    for j, packet in enumerate(out[:-1]):
        if type(packet) is list and len(packet) == 3:
            s, u, t = packet
            out[j] = [0 if u else s, s, u, t]
    return out


def to_three_fields(data, protocol="global"):
    """Regenerate canonical packets while replaying an inferred-major proof."""
    if protocol not in ("global", "local"):
        raise ValueError("Unknown protocol")
    result = copy.deepcopy(data)
    pending = list(enumerate(copy.deepcopy(data)))
    clock = 0
    events = []

    def has_binary(a):
        return isinstance(a, list) and (len(a) == 2 or any(map(has_binary, a)))

    def check(goal, context, floor=0):
        nonlocal clock

        def opening(tree, image=None, depth=0):
            if isinstance(tree, list):
                return [opening(child, image, depth + 5 - len(tree)) for child in tree]
            lower = clock if protocol == "global" else floor
            return tree if lower <= tree < depth else depth % 2 and opening(image, depth=3)

        while opening(goal) not in context:
            index, packet = pending.pop()
            major, source, seed, body = packet
            matched = opening(body, seed) == goal
            if matched:
                major = [source, seed] if source else [body] * 3
                goal = opening(body, source)
                triple = [source, seed, body]
                action = "equality_or_Q"
            elif major:
                if not has_binary(goal) or type(major) is not list or len(major) != 1:
                    raise ValueError("Not a canonical D-opening packet")
                triple = [major, 0, 0]
                action = "D_open"
            elif seed:
                if not has_binary(goal) or has_binary(body):
                    raise ValueError("Not a canonical computation packet")
                triple = [source, seed, body]
                action = "computation"
            else:
                if not has_binary(goal) or has_binary(body):
                    raise ValueError("Not a canonical introduction packet")
                triple = [0, seed, body]
                action = "introduction"
            result[index] = triple
            events.append({"index": index, "action": action})
            if protocol == "global":
                if major:
                    check(major, context)
                    hypothesis = major * 3
                elif seed:
                    hypothesis = [[source and [source], seed, body],
                                  opening(body, [source, seed, body], 3) if source else seed]
                else:
                    goal = opening(*goal, body, 2)
                    hypothesis = goal
                clock -= 1
                fresh = clock
            else:
                check(major, context, floor)
                if major:
                    hypothesis = major * 3
                elif seed:
                    hypothesis = [[source and [source], seed, body],
                                  opening(body, [source, seed, body], 3) if source else seed]
                else:
                    goal = opening(*goal, body, 2)
                    hypothesis = goal
                floor -= 1
                fresh = floor
            context += (opening(hypothesis, (major or len(goal) == 2) and fresh),)
            goal = opening(goal, [fresh])

    _, goal = pending.pop()
    check(goal, () if protocol == "global" else (0,))
    return result, {"protocol": protocol, "events": events, "unused_prefix_length": len(pending)}
