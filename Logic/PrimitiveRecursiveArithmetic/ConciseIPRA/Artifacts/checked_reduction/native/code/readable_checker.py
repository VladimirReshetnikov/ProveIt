"""Readable expansion of the complete 589-byte eager iPRA checker.

Input is a JSON list consumed from the end: its final item is the closed
native Eq/D goal, and each preceding consumed item is [source, seed,
body, major]. An empty list in the major field is the neutral premise.

The public formula and all numerical terms are validated. Certificate
internals use the inherited administrative integer/list syntax. Normal
exit with the line ACCEPT is acceptance; an exception is rejection.
"""
import json

MISSING = object()


def check(context, goal, floor=0):
    source, seed, body, major = next_packet()

    def opening(tree, image=MISSING, depth=0):
        # Only the root invocation starts with an empty context. Before
        # any recursive proof operation, the empty neutral is appended.
        if tree * 0 != 0 and (context or len(tree) in (1, 2 + depth % 2)):
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if floor <= tree < depth and (context or depth & (tree % 2)):
            return tree or 1
        # Eager image validation is intentional even when depth is even.
        return depth % 2 * opening(image, depth=3)

    validated_goal = opening(goal)
    context.append([])
    recursive_term = [source, seed, body]
    computation = [
        [source and [source] or 1, seed, body],
        opening(body, recursive_term, 3) if source else seed,
    ]
    # None is the return value of append in the compact tuple. Opening
    # returns integer/list trees, so None cannot supply a proof resource.
    if validated_goal in (None, *context, computation):
        return

    check(context, major, floor)
    hypothesis = major * 3
    if not hypothesis:
        goal = opening(*goal, body, 2)
        hypothesis = goal

    # Evaluate len even when major is truthy, matching the compact tuple.
    atomic_progress = len(goal) == 2 == seed
    progressive = bool(major) or atomic_progress
    floor -= 1
    hypothesis = opening(hypothesis, progressive * floor)

    # Both instances are evaluated before the equality test, as in the
    # compact expression. This order preserves all freshness checks.
    minor = opening(body, source)
    required_major = [source, seed] if source else [body] * 3
    target = opening(body, seed)
    if (major, goal) == (required_major, target):
        goal = minor
    goal = opening(goal, [floor])
    check(context + [hypothesis], goal, floor)


certificate = json.load(open(0))
if str(certificate).strip('0123456789-[], '):
    raise ValueError('The complete JSON input must use exact integers and lists')
next_packet = certificate.pop
check([], next_packet())
print('ACCEPT')
