"""Explicit hardness construction. These synthetic inputs are not manifold cores."""
from .model import make_instance


def cnf_instance(variables: int, clauses: list[list[int]]):
    """Encode a nonempty CNF in a rooted-star dual graph with loops.

    Tree rows 2*i and 2*i+1 select respectively x_(i+1)=True and False.
    Every matrix column has at most three nonzeros, all in {1,2}.
    """
    if type(variables) is not int or variables < 1 or not clauses:
        raise ValueError('positive variable count and nonempty clause list required')
    if any(type(lit) is not int or lit == 0 or abs(lit) > variables
           for clause in clauses for lit in clause):
        raise ValueError('invalid literal')
    edges = [(0, i+1) for i in range(variables) for _ in range(2)]
    rows = [{} for _ in edges]
    labels = [f'{sign}x{i+1}' for i in range(variables) for sign in ('+', '-')]
    next_column = 0

    def row(label):
        r = len(rows)
        rows.append({})
        edges.append((0, 0))
        labels.append(label)
        return r

    def implication(prerequisites, target):
        nonlocal next_column
        for r in prerequisites:
            rows[r][next_column] = 2
        rows[target][next_column] = 1
        next_column += 1

    clause_rows = []
    for i, clause in enumerate(clauses):
        c = row(f'clause_{i}')
        clause_rows.append(c)
        for literal in clause:
            literal_row = 2*(abs(literal)-1) + (literal < 0)
            implication([literal_row], c)
    layer = clause_rows
    while len(layer) > 1:
        nxt = []
        for i in range(0, len(layer), 2):
            if i + 1 == len(layer):
                nxt.append(layer[i])
            else:
                target = row(f'and_{len(rows)}')
                implication(layer[i:i+2], target)
                nxt.append(target)
        layer = nxt
    accept = layer[0]
    for literal_row in range(2*variables):
        implication([accept], literal_row)
    return (make_instance(variables+1, edges, rows, columns=next_column),
            dict(row_labels=labels, accept_row=accept, clause_rows=clause_rows))
