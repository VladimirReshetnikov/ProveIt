"""Sound abstract source transitions; adapted from ProveIt verify_joint_mask.py."""

def successors(row, mask):
    """Sound transitions: bit j is 1 iff register j is strictly positive."""
    op = row[0]
    if op == 'halt':
        return ()
    if op == 'jump':
        return ((row[1], mask),)
    if op == 'inc':
        return ((row[2], mask | (1 << row[1])),)
    if op == 'dec':
        bit = 1 << row[1]
        if mask & bit:
            # A positive register becomes either zero or remains positive.
            return ((row[3], mask & ~bit), (row[3], mask))
        return ((row[2], mask),)
    raise ValueError(f'unknown operation {op}')

