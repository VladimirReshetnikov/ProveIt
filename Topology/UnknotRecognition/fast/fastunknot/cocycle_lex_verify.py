"""Independent arithmetic and source-bound primitive connected-surface replay."""
from .integer_codec import encoded_integer,certificate_equal
from .cocycle_euler_verify import verify_difference_optimum
from .cocycle_span_verify import verify_cocycle_span
from .cocycle_lex_geometry import edge_model,span_network,span_value
from .normal_surface_geometry import _prepare,_coordinates,NormalOrbitError


def _inspect_edge_span(prepared,heights,certificate,check):
    fields={'schema','vertex_ids','primary','secondary','normal_pieces','euler_characteristic'}
    if type(certificate) is not dict or set(certificate)!=fields or certificate['schema']!='normal-cocycle-edge-span-v1':return None
    labels,vertices,h,edges=edge_model(prepared,heights,check);n=len(labels)
    if not certificate_equal(certificate['vertex_ids'],labels):return None
    primary=certificate['primary']
    if not verify_difference_optimum(n,edges,[],primary,check=check):return None
    secondary=certificate['secondary']
    if type(secondary) is not dict or set(secondary)!={'kind','certificate'}:return None
    proof=secondary['certificate']
    if secondary['kind']=='network':
        first_p=[encoded_integer(v) for v in primary['potential']]
        objective,constraints,initial=span_network(vertices,h,edges,primary['edge_flows'],first_p,check)
        if not verify_difference_optimum(len(initial),objective,constraints,proof,check=check):return None
        potential=[encoded_integer(v) for v in proof['potential'][:n]]
        expected_span=encoded_integer(proof['objective'])
    elif secondary['kind']=='minimum-span':
        global_vertices=[[labels[v] for v in row] for row in vertices]
        if not verify_cocycle_span(global_vertices,h,proof,check=check):return None
        potential=[encoded_integer(v) for v in proof['potential']]
        expected_span=encoded_integer(proof['disc_count'])
    else:return None
    value=0
    for a,b,c,w in edges:
        check();value+=w*abs(c+potential[b]-potential[a])
    span=span_value(vertices,h,potential,check)
    if value!=encoded_integer(primary['objective']) or span!=expected_span:return None
    if (not certificate_equal(certificate['normal_pieces'],span)
            or type(certificate['euler_characteristic']) is bool):return None
    try:chi=encoded_integer(certificate['euler_characteristic'])
    except ValueError:return None
    if 2*chi!=2*span-value:return None
    return dict(vertex_ids=labels,potential=potential,normal_pieces=span,euler_characteristic=chi)


def verify_cocycle_edge_span(triangulation,heights,certificate,*,check=lambda:None):
    error=[None]
    def checked():
        try:check()
        except BaseException as exc:error[0]=exc;raise
    try:
        answer=_inspect_edge_span(_prepare(triangulation,checked),heights,certificate,checked) is not None
        if error[0] is not None:raise error[0]
        return answer
    except NormalOrbitError:
        if error[0] is not None:raise
        return False


def _inspect_lex_source_impl(diagram,certificate,source_check,check):
    from .diagram import Diagram,DiagramError
    from .normal_cocycle_verify import _primitive_cochain
    fields={'schema','input_pd','triangulation','heights','coordinates','optimality_certificate'}
    check()
    if type(certificate) is not dict or set(certificate)!=fields or certificate['schema']!='diagram-cocycle-lex-v1':return None
    try:source=Diagram.from_pd(diagram.pd)
    except (DiagramError,AttributeError,TypeError):return None
    if not certificate_equal(certificate['input_pd'],[list(row) for row in source.pd]):return None
    raw=certificate['triangulation']
    if not source_check(source,raw,check=check):return None
    prepared=_prepare(raw,check)
    arithmetic=_inspect_edge_span(prepared,certificate['heights'],certificate['optimality_certificate'],check)
    if arithmetic is None:return None
    heights=[[encoded_integer(v) for v in row] for row in certificate['heights']]
    if _primitive_cochain(prepared,heights,False,check) is None:return None
    labels=arithmetic['vertex_ids'];lookup=dict(zip(labels,arithmetic['potential']))
    adjusted=[[z+lookup[prepared['vertex_roots'][4*t+i]] for i,z in enumerate(row)] for t,row in enumerate(heights)]
    analysed=_coordinates(prepared,certificate['coordinates'],check)
    values=_primitive_cochain(prepared,adjusted,False,check)
    if values is None or any(analysed['weights'][edge]!=abs(v) for edge,v in values.items()):return None
    chi=analysed['euler_characteristic']
    if chi!=arithmetic['euler_characteristic'] or analysed['normal_disks']!=arithmetic['normal_pieces']:return None
    return (dict(components=1,orientable_components=1,euler_characteristic=chi,
        normal_pieces=analysed['normal_disks'],compressing_discs=int(chi==1),
        cappable_annulus=chi==0,connectivity='edge-then-span'),prepared,analysed)


def _inspect_lex_source(diagram,certificate,source_check,*,check=lambda:None):
    error=[None]
    def checked():
        try:check()
        except BaseException as exc:error[0]=exc;raise
    try:
        answer=_inspect_lex_source_impl(diagram,certificate,source_check,checked)
        if error[0] is not None:raise error[0]
        return answer
    except NormalOrbitError:
        if error[0] is not None:raise
        return None


def inspect_lex_cocycle_certificate(diagram,certificate,*,check=lambda:None):
    from .diagram_exterior_verify import verify_diagram_exterior
    answer=_inspect_lex_source(diagram,certificate,verify_diagram_exterior,check=check)
    return None if answer is None else answer[0]
