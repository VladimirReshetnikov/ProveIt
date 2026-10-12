"""Independent finite verifiers; imports neither graph producer nor scheduler.

Checks graph/trace semantics only. It does not certify a 3-manifold embedding,
a native normal-cut source map, compression admissibility, or knot triviality.
"""
from collections import deque


def _nat(x, minimum=0):
    return type(x) is int and x >= minimum


def _walk(n, edges, ids, start=0):
    adj = [[] for _ in range(n)]
    for e in ids:
        a, b = edges[e]
        adj[a].append((b, e)); adj[b].append((a, e))
    seen = {start}; q = deque([start])
    while q:
        u = q.popleft()
        for v, _ in adj[u]:
            if v not in seen:
                seen.add(v); q.append(v)
    return seen, adj


def verify_batch(packet):
    try:
        if packet['schema'] != 'cographic-batch-v1':
            return False
        if packet['scope'] != 'relative-to-authenticated-chamber-graph':
            return False
        g = packet['graph']; n = g['vertices']; edges = g['edges']; w = g['weights']
        if not _nat(n, 1) or len(w) != len(edges) or not all(_nat(x) for x in w):
            return False
        if n > len(edges)+1:
            return False
        for edge in edges:
            if len(edge) != 2 or not all(_nat(x) and x < n for x in edge):
                return False
        tree = packet['tree']; chosen = packet['chosen']; m = len(edges)
        if not all(_nat(e) and e < m for e in tree + chosen):
            return False
        if len(set(tree)) != len(tree) or len(set(chosen)) != len(chosen):
            return False
        if set(tree) & set(chosen) or set(tree) | set(chosen) != set(range(m)):
            return False
        if len(tree) != n-1:
            return False
        seen, adj = _walk(n, edges, tree)
        if len(seen) != n:
            return False
        if not _nat(packet['reward']) or packet['reward'] != sum(w[e] for e in chosen):
            return False
        # Independent cycle-property MST certificate; O(m*n) graph work.
        for e in chosen:
            a, b = edges[e]
            q = deque([(a, 0)]); visited = {a}; pathmax = None
            while q:
                x, mx = q.popleft()
                if x == b:
                    pathmax = mx; break
                for y, t in adj[x]:
                    if y not in visited:
                        visited.add(y); q.append((y, max(mx, w[t])))
            if pathmax is None or pathmax > w[e]:
                return False
        return True
    except (KeyError, IndexError, TypeError, ValueError):
        return False


def verify_routing(packet):
    try:
        if packet['schema'] != 'finite-routing-forest-v1':
            return False
        n = packet['atom_count']; interior = packet['interior']; gates = packet['gates']
        if not _nat(n, 1) or not verify_batch(packet['batch']):
            return False
        if n > len(interior)+len(gates)+1:
            return False
        for e in interior + gates:
            if len(e) != 2 or not all(_nat(x) and x < n for x in e):
                return False
        # Discover chambers independently with breadth-first search.
        _, adj = _walk(n, interior, range(len(interior)))
        labels = [-1]*n; c = 0
        for root in range(n):
            if labels[root] >= 0:
                continue
            labels[root] = c; todo = [root]
            while todo:
                x = todo.pop()
                for y, _ in adj[x]:
                    if labels[y] < 0:
                        labels[y] = c; todo.append(y)
            c += 1
        claimed = packet['batch']['graph']
        if claimed['vertices'] != c or len(claimed['edges']) != len(gates):
            return False
        # Vertex numbering may differ; verify a bijective relabelling.
        image = {}; inverse = {}
        for (u,v), (a,b) in zip(gates, claimed['edges']):
            for x,y in [(labels[u], a), (labels[v], b)]:
                if (x in image and image[x] != y) or (y in inverse and inverse[y] != x):
                    return False
                image[x] = y; inverse[y] = x
        if gates and len(image) != c:
            return False
        f = packet['forest']
        if not all(_nat(e) and e < len(interior) for e in f) or len(set(f)) != len(f):
            return False
        tree = f + [len(interior)+e for e in packet['batch']['tree']]
        if len(tree) != n-1:
            return False
        reached, _ = _walk(n, interior+gates, tree)
        return len(reached) == n
    except (KeyError, IndexError, TypeError, ValueError):
        return False


def verify_trace(caps, parents, events, initial=None):
    """Replay a fixed-DAG persistent counter trace with topological slot IDs."""
    try:
        n = len(caps)
        if len(parents) != n or not all(_nat(g) for g in caps):
            return False
        for i, ps in enumerate(parents):
            if len(set(ps)) != len(ps) or not all(_nat(j) and j < i for j in ps):
                return False
        initial = tuple(caps if initial is None else initial)
        if len(initial) != n or any(not _nat(d) or d > g for d,g in zip(initial,caps)):
            return False
        versions = [0]*n; remaining = list(initial)
        snapshots = [tuple(0 for _ in ps) for ps in parents]
        for op, i in events:
            if not _nat(i) or i >= n:
                return False
            clean = []
            for j, ps in enumerate(parents):
                clean.append(all(clean[p] for p in ps) and
                             snapshots[j] == tuple(versions[p] for p in ps))
            if op == 'repair':
                if not clean[i] or remaining[i] == 0:
                    return False
                remaining[i] -= 1
            elif op == 'rebuild':
                if clean[i] or not all(clean[p] for p in parents[i]):
                    return False
                # A genuinely new parent snapshot is required.
                now = tuple(versions[p] for p in parents[i])
                if now == snapshots[i]:
                    return False
                remaining[i] = caps[i]; snapshots[i] = now
            else:
                return False
            versions[i] += 1
        bound = []
        for i, ps in enumerate(parents):
            bound.append(initial[i] + (caps[i]+1)*sum(bound[p] for p in ps))
        return all(v <= b for v,b in zip(versions, bound))
    except (TypeError, ValueError, IndexError):
        return False


def verify_reuse(packet):
    """Independently check the composite fixed-DAG optimization certificate."""
    try:
        if packet['schema'] != 'cographic-causal-reuse-v1':
            return False
        if packet['scope'] != 'relative-to-authenticated-geometry-and-fixed-dependencies':
            return False
        caps=packet['caps']; parents=packet['parents']; costs=packet['event_costs']
        n=len(caps)
        if len(parents)!=n or len(costs)!=n or not all(_nat(x) for x in caps+costs):
            return False
        for i,ps in enumerate(parents):
            if len(set(ps))!=len(ps) or not all(_nat(j) and j<i for j in ps):
                return False
        batch=packet['batch']
        if not verify_batch(batch):
            return False
        k=len(batch['graph']['edges'])
        tasks=packet['candidate_tasks']; saved=packet['saved_progress']
        if len(tasks)!=k or len(set(tasks))!=k or not all(_nat(t) and t<n for t in tasks):
            return False
        if len(saved)!=k or any(not _nat(s) or s>caps[t] for s,t in zip(saved,tasks)):
            return False
        # Recompute reverse scores independently from the producer module.
        a=list(costs)
        for j in reversed(range(n)):
            for i in parents[j]:
                a[i]+=(caps[j]+1)*a[j]
        if packet['amplification']!=a:
            return False
        if batch['graph']['weights']!=[s*a[t] for s,t in zip(saved,tasks)]:
            return False
        d=list(caps)
        for e in batch['chosen']:
            d[tasks[e]]-=saved[e]
        if packet['initial_after_retention']!=d:
            return False
        before=[]; after=[]
        for i,ps in enumerate(parents):
            before.append(caps[i]+(caps[i]+1)*sum(before[j] for j in ps))
            after.append(d[i]+(caps[i]+1)*sum(after[j] for j in ps))
        wb=sum(p*b for p,b in zip(costs,before)); wa=sum(p*b for p,b in zip(costs,after))
        return (_nat(packet['baseline_work_bound']) and _nat(packet['retained_work_bound'])
                and packet['baseline_work_bound']==wb and packet['retained_work_bound']==wa
                and wb-wa==batch['reward'])
    except (KeyError, IndexError, TypeError, ValueError):
        return False
