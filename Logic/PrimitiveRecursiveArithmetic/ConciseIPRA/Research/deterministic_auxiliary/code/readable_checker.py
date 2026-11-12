"""Self-contained readable checker for a source-selected elimination and deterministic introduction.

The public input is a JSON array: instructions followed by the goal.  An
instruction has [major, source, initializer_or_mode, template_or_witness].
Instructions are consumed from right to left; unused prefix data is inert.
Normal exit with exactly ACCEPT is success; an exception rejects the input.

Canonical numerical zero is raw 0. Raw [0] denotes S(0).
Equality transport from literal zero is derived by the supplied normalizer.
The empty-array formula [] is an administrative spelling of the theorem 0=0.
The kernel does not import a producer, database, or verification helper.
"""
from json import load


def check(goal, assumptions=([],), floor=0):
    def open_tree(tree, image=None, depth=0):
        try:
            return [open_tree(child, image, depth + 5 - len(tree))
                    for child in tree]
        except:
            if floor <= tree < depth:
                return tree
            # Formula padding stays truth. Numerical images are scope-checked.
            return depth % 2 and open_tree(image, depth=3)

    while open_tree(goal) not in assumptions:
        major, source, initializer_or_mode, template_or_witness = instruction()

        # These calculations are pure: the major is still checked below.
        # The source field selects precisely one possible elimination major.
        expected_major = ([source, initializer_or_mode] if source
                          else [template_or_witness] * 3)
        if major == expected_major:
            if open_tree(template_or_witness, initializer_or_mode) == goal:
                goal = open_tree(template_or_witness, source)

        check(major, assumptions, floor)
        exported = major * 3
        if exported:
            # A D major exports Q; other array arities export only padding.
            hypothesis = exported
        elif initializer_or_mode:
            counter = source and [source]
            lhs = [counter, initializer_or_mode, template_or_witness]
            rhs = (open_tree(template_or_witness,
                             [source, initializer_or_mode, template_or_witness], 3)
                   if source else initializer_or_mode)
            hypothesis = [lhs, rhs]
        else:
            # Exact argument unpacking requires a unary D goal.
            goal = open_tree(*goal, template_or_witness, 2)
            hypothesis = goal

        floor -= 1
        # There is no introduction-mode choice. A literal equation has
        # even root arity (progress); a compound has odd root arity (cases).
        image = (major or not len(goal) % 2) and floor
        assumptions += (open_tree(hypothesis, image),)
        goal = open_tree(goal, [floor])


instruction = load(open(0)).pop
check(instruction())
print('ACCEPT')
