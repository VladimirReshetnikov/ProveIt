def guarded_graph(sites):
    leaves = {pc: i for i, (pc, op, reg) in enumerate(sites)}
    prefixes = {pc[:k] for pc in leaves for k in range(len(pc) + 1)}
    def first(pc):
        while pc not in prefixes:
            assert pc.endswith('0')
            pc = pc[:-1]
        while pc not in leaves:
            pc += '0'
        return leaves[pc]
    def after(pc):
        pc = pc.rstrip('1')
        return pc[:-1] + '1' if pc else ''
    def ancestor(pc, bit, count):
        for _ in range(count):
            j = pc.rfind(bit)
            if j < 0:
                return ''
            pc = pc[:j]
        return pc
    graph = []
    for pc, op, reg in sites:
        if op == 'CI':
            graph.append([op, reg, first(after(pc))])
        elif op == 'CD':
            graph.append([op, reg, first(after(ancestor(pc, '0', 1))), first(after(pc))])
        elif op == 'CB':
            graph.append(['CONTROL', first(after(ancestor(pc, '0', reg)))])
        elif op == 'CC':
            graph.append(['CONTROL', first(ancestor(pc, '1', reg))])
        else:
            assert op == 'CH', (pc, op, reg)
            graph.append(['HALT'])
    return graph

