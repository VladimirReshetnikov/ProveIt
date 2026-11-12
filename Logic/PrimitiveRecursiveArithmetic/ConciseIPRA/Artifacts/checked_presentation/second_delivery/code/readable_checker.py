"""Readable standalone expansion of checker_strict.py.

Input: one JSON array, read from its right end. Its last element is a
canonical closed formula built from equality and the paired binder D.
Every consumed instruction has four fields [major, source, seed, body].
The entire input, including unused prefix entries, must contain only
exact integers and lists. No local checker or other package is imported.

The weighted syntax is explained in the report. In particular, equation
nodes have two children, D nodes one, successor nodes one, and iterator
nodes three. Auxiliary proof trees may use administrative syntax aliases;
only the public goal receives the canonical grammar check.

This version favors names and explicit evaluation order. It is not a
benchmark-minimal source. Normal exit printing ACCEPT is acceptance;
an exception is rejection. No assertion is used as a checking condition.
"""
import json


def integer_list_tree(value):
    """Exclude bool, float, strings, objects and null, even in unused data."""
    return type(value) is int or (
        type(value) is list and all(integer_list_tree(child) for child in value)
    )


def check_proof(goal, context, packets, floor=0, public=False):
    """Check a goal using immutable local contexts and a shared input stack.

    The integer floor is the lowest already allocated rigid parameter.
    Only this call's continuation decrements its floor. A recursive major
    proof therefore cannot leak its local hypotheses or new parameters.
    """
    def opening(tree, image=None, depth=0):
        """Validate scope and replace an exposed numerical slot by image.

        The parity of depth distinguishes numerical positions (odd) from
        formula positions (even). An array adds 5 minus its arity to depth.
        Public mode additionally enforces the canonical Eq/D term grammar.
        A missing numerical image raises instead of erasing a scope error.
        """
        if type(tree) is list:
            arity = len(tree)
            if public:
                allowed = (1, 3) if depth % 2 else (1, 2)
                if arity not in allowed:
                    raise ValueError("Invalid arity in the public formula")
            child_depth = depth + 5 - arity
            return [opening(child, image, child_depth) for child in tree]

        if type(tree) is not int:
            # The input alphabet was checked before execution. Reaching
            # this branch means an absent numerical image was requested.
            raise ValueError("An out-of-scope numerical occurrence has no image")

        in_scope = floor <= tree < depth
        if public:
            canonical_leaf = depth % 2 and (
                tree == 0 or (tree > 1 and tree % 2 == 1)
            )
            if not in_scope or not canonical_leaf:
                raise ValueError("Invalid or unbound leaf in the public formula")
            return tree
        if in_scope:
            return tree
        if depth % 2:
            return opening(image, depth=3)
        return 0

    # This scan is essential: unchecked raw majors can acquire a different
    # meaning when their out-of-scope coordinates are subsequently opened.
    if opening(goal) in context:
        return

    major, source, seed, body = packets.pop()
    public = False

    # The major is proved in the unchanged parent context and old scope.
    # Even a neutral major is checked; the initial context retains 0.
    check_proof(major, context, packets, floor)

    if major:
        # A unary D major becomes its auxiliary three-child Q resource.
        # Other admitted administrative arities keep their inherited reading.
        hypothesis = major * 3
    elif seed:
        counter = [source] if source else source
        iterator = [counter, seed, body]
        if source:
            recursive_iterator = [source, seed, body]
            endpoint = opening(body, recursive_iterator, 3)
        else:
            endpoint = seed
        hypothesis = [iterator, endpoint]
    else:
        # Canonical introductions have a unary goal. Keep the exact star
        # expansion here to preserve administrative integer/list behavior.
        goal = opening(*goal, body, 2)
        hypothesis = goal

    # Preserve the full-native selector exactly. For example, raw seed []
    # and raw seed 0 are both falsy but need not select the same rule mode.
    # The selector is evaluated before allocation changes the floor.
    fresh_image = bool(major or len(goal) % 2 == seed)
    floor -= 1
    image = floor if fresh_image else 0
    opened_hypothesis = opening(hypothesis, image)
    extended_context = context + [opened_hypothesis]

    # Both template endpoints are evaluated eagerly at the NEW floor.
    # This order follows the compact program's tuple construction exactly.
    source_instance = opening(body, source)
    expected_major = [source, seed] if source else [body] * 3
    target_instance = opening(body, seed)
    if (major, goal) == (expected_major, target_instance):
        continuation_goal = source_instance
    else:
        continuation_goal = goal

    continuation_goal = opening(continuation_goal, [floor])
    check_proof(continuation_goal, extended_context, packets, floor)


def main():
    packets = json.load(open(0))
    if type(packets) is not list or not integer_list_tree(packets):
        raise ValueError("Expected a JSON array of exact-integer/list trees")
    goal = packets.pop()
    check_proof(goal, [0], packets, public=True)
    print("ACCEPT")


if __name__ == "__main__":
    main()
