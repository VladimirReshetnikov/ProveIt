"""Record-level integration seam, pinned to ProveIt e0b2f802f336fcb51e9ec5f29174cfe28dfb9d39.

These functions DO NOT authenticate source geometry. A caller must obtain counts
and endpoints from authenticated source charts, then invoke the maintained
replay_core_three_handles and all downstream whole-cut/pattern verifiers.
No native production module is imported or patched by this file.
"""
from copy import deepcopy
from activation_forest import Instance, verify_positive


def _endpoints(ids, records):
    ids = sorted(ids)
    if len(ids) != len(set(ids)) or any(type(x) is not int or x < 0 for x in ids):
        raise ValueError('invalid three-handle identifiers')
    owners = {x:i+1 for i,x in enumerate(ids)}
    owners[None] = 0
    edges=[]
    for i,record in enumerate(records):
        if type(record) is not dict or set(record) != {'two_handle','ends'}:
            raise ValueError('malformed source endpoint record')
        if type(record['two_handle']) is not int or record['two_handle'] != i:
            raise ValueError('source records must use contiguous IDs in source order')
        pair=record['ends']
        if type(pair) not in (list,tuple) or len(pair)!=2:
            raise ValueError('each source edge must retain both endpoint occurrences')
        if any(x is not None and (type(x) is not int or x not in owners) for x in pair):
            raise ValueError('unknown endpoint owner')
        edges.append(tuple(owners[x] for x in pair))
    return ids,tuple(edges)


def from_native_records(counts, three_handle_ids, records):
    ids,edges=_endpoints(three_handle_ids,records)
    if type(counts) is not dict or set(counts)!=set(range(len(edges))) or any(type(x) is not int for x in counts):
        raise ValueError('counts must retain the contiguous source row range')
    labels=set()
    for row in counts.values():
        if type(row) is not dict:
            raise ValueError('each source row must map one-handle labels to unsigned counts')
        for h,value in row.items():
            if type(h) is not int or h<0 or type(value) is not int or value<0:
                raise ValueError('invalid unsigned source incidence')
            labels.add(h)
    labels=sorted(labels)
    matrix=tuple(tuple(counts[e].get(h,0) for h in labels) for e in range(len(edges)))
    return Instance(len(ids)+1,edges,matrix,len(labels)), ids, labels


def native_proposal(inst, certificate, three_handle_ids, records):
    ids,edges=_endpoints(three_handle_ids,records)
    if edges!=inst.edges or len(ids)+1!=inst.vertices:
        raise ValueError('local input is not bound to these source endpoint records')
    if not verify_positive(inst,certificate):
        raise ValueError('local positive certificate rejected')
    return dict(schema='core-three-handle-reduction-v1', dual_endpoints=deepcopy(records),
                cancellations=[dict(two_handle=e,three_handle=ids[v-1])
                               for e,v in certificate['dual_order']],
                surviving_two_handles=[e for e in range(inst.m) if e not in set(certificate['tree'])])
