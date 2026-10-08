"""Run in a checkout of the pinned upstream API. Not run during artifact build.

PYTHONPATH=src:/path/to/ProveIt/Topology/UnknotRecognition/fast \
    python integration/upstream_check.py
"""
import json
from fastunknot.braid import braid_certificate
from ranktwo.families import sleeved_unknot
from fastunknot_adapter import braid_gateway_with_ranktwo

rows=[]
for strands in (4,5,8,20):
    for m in (1,4,16,64):
        word=sleeved_unknot(strands,m)
        before=braid_certificate(strands,word)
        after=braid_gateway_with_ranktwo(strands,word)
        assert before['status']=='INCONCLUSIVE'
        assert after['status']=='UNKNOT'
        assert len(after['reduced_input']['word'])==strands-1
        rows.append({'strands':strands,'m':m,'letters':len(word),
                     'before':before['status'],'after':after['status']})
print(json.dumps({'cases':len(rows),'rows':rows},indent=2))
