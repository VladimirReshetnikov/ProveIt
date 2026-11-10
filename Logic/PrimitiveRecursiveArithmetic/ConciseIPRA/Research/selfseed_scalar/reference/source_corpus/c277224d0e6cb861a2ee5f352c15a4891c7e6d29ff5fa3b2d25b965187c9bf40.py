"""Independent standard-model diagnostic, adapted from the flat draft decoder.

This is a finite falsification attempt, not an interpretation proof. The
candidate checker imports none of this file. Each successful generation
is tested at several assignments to every admitted fresh parameter.
"""
import itertools
import math

class Budget(Exception):
    pass

class Generator:
    def __init__(self, floor):
        self.floor = floor

    def open(self, tree, image=None, depth=0):
        if isinstance(tree, list):
            return [self.open(child, image, depth + b' \x02\x01\x04'[len(tree)])
                    for child in tree]
        if self.floor <= tree < depth:
            return tree
        return depth % 2 and self.open(image, depth=1)

    def equation(self, predecessor, seed, update):
        if predecessor:
            source = [[predecessor], seed, update]
            result = self.open(update, [predecessor, seed, update], 1)
        else:
            source, result = [predecessor, seed, update], seed
        self.floor -= 1
        return self.open([source, result], 0)

def value(tree, slots, parameters, budget):
    budget[0] -= 1
    if budget[0] < 0:
        raise Budget
    if isinstance(tree, list):
        if not tree or len(tree) == 2:
            return 0
        if len(tree) == 1:
            return 1 + value(tree[0], (0,) + slots, parameters, budget)
        if len(tree) != 3:
            raise ValueError('Numerical arity')
        counter, seed, update = tree
        count = value(counter, (0,0) + slots, parameters, budget)
        state = value(seed, (0,0) + slots, parameters, budget)
        if count > 300:
            raise Budget
        for _ in range(count):
            state = value(update, (state,state) + slots, parameters, budget)
        return state
    coordinate = math.floor(tree)
    if coordinate < 0:
        return parameters[coordinate]
    return 0 if coordinate == 0 else slots[(coordinate-1)//2]

def audit():
    predecessors = [0, [], False, 0.0, 0.5, 1, 2, 3, 4, 5, -1, -2, -3,
                    [0], [1], [-1], [0,0], [0,0,0], [0,-1,0], [[0],0,1],
                    None, {}, 'x']
    seeds = [0, [], False, 0.5, 1, 3, 5, -1, -2, -3, [0], [[0]],
             [0,-1,0], [[0],0,1], None, {}]
    updates = [0, [], False, 0.5, 1, 2, 3, 4, 5, 7, -1, -2, -3,
               [0], [1], [3], [[5]], [0,0], [0,1], [0,1,0],
               [[0],1,1], [1,0,[1]], [0,-1,0], None, {}]
    counts = dict(attempted=0, generated=0, evaluated=0, budget_skips=0,
                  counterexamples=0)
    for old_floor in (0,-1,-3):
        for predecessor,seed,update in itertools.product(predecessors,seeds,updates):
            counts['attempted'] += 1
            generator=Generator(old_floor)
            try:
                equation=generator.equation(predecessor,seed,update)
            except (TypeError,ValueError,IndexError,RecursionError):
                continue
            counts['generated'] += 1
            for parameter_value in (0,1,2,5):
                parameters={j:parameter_value for j in range(old_floor-1,0)}
                try:
                    left=value(equation[0],(),parameters,[15000])
                    right=value(equation[1],(),parameters,[15000])
                except Budget:
                    counts['budget_skips'] += 1
                    continue
                counts['evaluated'] += 1
                if left != right:
                    raise AssertionError(('False generated equation',old_floor,
                                          predecessor,seed,update,equation,parameters,left,right))
    return counts

if __name__ == '__main__':
    import json
    print(json.dumps(audit(),indent=2))
