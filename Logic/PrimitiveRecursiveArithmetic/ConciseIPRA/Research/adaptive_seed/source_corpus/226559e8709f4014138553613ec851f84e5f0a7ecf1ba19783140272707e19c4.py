"""Complete explicit-endpoint checker, with descriptive fields and errors.

The compact kernels implement this same proof format. This reference keeps
all rejection paths explicit and is not the source-size record. Only JSON
is imported. A proof producer, converter, or mathematical library is never
trusted or imported here.
"""
from json import load

k = 0


def i(tree, image=None, depth=0):
    """Validate/open a sorted tree using the inherited protected-slot syntax."""
    if isinstance(tree, list):
        return [i(child, image, depth + b" \2\1\4"[len(tree)])
                for child in tree]
    if k <= tree < depth:
        return tree
    if depth % 2:
        return i(image, depth=1)
    return 0


def c(goal, context):
    """Return normally exactly when this proof subtree checks; otherwise raise."""
    global k
    if i(goal) in context:
        return

    major, source, target, template = q()
    if major:
        c(major, context)
        is_equality = major == [source, target]
        is_closure = not source and major == [template]
        if is_equality or is_closure:
            if i(template, target) != goal:
                raise ValueError("Elimination target is not the requested goal")
            c(i(template, source), context)
            return
        if not isinstance(major, list) or len(major) != 3:
            raise ValueError("Elimination data do not match the proved major")
        local_hypothesis = [major[2]]
    elif template:
        local_hypothesis = goal = i(goal[2], template, 2)
    else:
        (counter, seed, update), result = goal
        if counter:
            predecessor, = counter
            seed = i(update, [predecessor, seed, update], 1)
        if result != seed:
            raise ValueError("Computation equation has the wrong result")
        return

    k -= 1
    hypothesis_image = k if major or len(goal) % 2 == major else 0
    c(i(goal, [k]), context + [i(local_hypothesis, hypothesis_image)])


try:
    q = load(open(0)).pop
    c(q(), [])
except:
    print("REJECT")
    raise
print("ACCEPT")
