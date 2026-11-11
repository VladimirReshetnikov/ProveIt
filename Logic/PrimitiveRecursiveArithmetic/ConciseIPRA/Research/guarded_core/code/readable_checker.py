"""Readable root-deterministic proof checker; only JSON parsing is imported.

Acceptance means exit status zero and exactly ACCEPT on standard output.
For canonical formulas, atomic D matrices have a provable zero instance:
D_xy(I(y,0;u.h)=I(y,0;u.k)).  The ordinary reading of these is
exists x (B(x,0) -> forall y B(x,y)); progress supplies their introduction.

Raw unguarded atomic D is administrative syntax read as
exists x forall y (B(x,y) -> B(x,Sy)), not as the old conditional closure.
Its elimination exports the weaker Q resource, justified by equation
induction in iPRA.  Completeness and bi-interpretation are claimed only
for the guarded canonical object language.  No checker imports a
producer, validator, axiom database, theorem catalog, or metatheory module.
"""
import json


def check(goal, context=[[]], floor=0):
    """The persistent context is never mutated; [] denotes derived 0=0."""
    def opening(tree, image=0j, depth=0):
        if isinstance(tree, list):
            return [opening(child, image, depth + 5 - len(tree))
                    for child in tree]
        if floor <= tree < depth:
            return tree
        return depth % 2 and opening(image, depth=3)

    if opening(goal) in context:
        return

    major, source, initializer, template = instruction()
    check(major, context, floor)

    # The same continuation implements equality transport and Q use.
    if major in ([source, initializer], not source and [template] * 3):
        if opening(template, initializer) == goal:
            replacement = opening(template, source)
            if replacement:
                goal = replacement

    if major:
        # A unary D exports Q; other nonempty arities export truth aliases.
        local = major * 3
    elif initializer:
        # Construct a zero or successor computation hypothesis.
        counter = source and [source]
        recursive = [source, initializer, template]
        endpoint = opening(template, recursive, 3) if source else initializer
        local = [[counter, initializer, template], endpoint]
    else:
        # Open the supplied witness before allocating the eigenparameter.
        local = goal = opening(*goal, template, 2)

    floor -= 1
    # The matrix root now determines the sole introduction rule.
    # Even meaningful arity is equality: use the progress hypothesis.
    # Odd meaningful arity is compound: retain its zero instance.
    image = floor if major or len(goal) % 2 == 0 else 0
    check(opening(goal, [floor]),
          context + [opening(local, image)], floor)


instruction = json.load(open(0)).pop
check(instruction())
print('ACCEPT')
