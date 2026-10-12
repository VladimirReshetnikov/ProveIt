import bootstrap
import json
from fastunknot.normal_weight_clusters import cluster_defect_search, enumerate_cluster_candidates
from normal_orbit_research.fixtures import layered_torus

record = json.loads((bootstrap.REPO/'synthesis/data/coherent-obstruction-certificate.json').read_text())
for name, raw, k in [('one', layered_torus(1)[0], 1),
                     ('two', layered_torus(2)[0], 2),
                     ('obstruction', record['moves'][-1]['triangulation'], 2)]:
    result = enumerate_cluster_candidates(raw, max_defect=k)
    print(name, result['status'], len(result.get('coordinates', [])), result['stats'], flush=True)
    result = cluster_defect_search(raw, max_defect=k)
    print('search', result['status'], result.get('cancellation_edges'), result['stats'], flush=True)
