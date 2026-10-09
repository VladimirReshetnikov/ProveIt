"""One isolated exact external-engine query; invoked by normal_surface.py."""
import json
import sys


def decide(request):
    import regina
    from importlib.metadata import version
    from .diagram import Diagram
    from .normal_surface import input_digest, regina_pd

    diagram = Diagram.from_pd(request['pd'])
    if input_digest(diagram.pd) != request['input_digest']:
        raise ValueError('normal-surface input digest mismatch')
    regina.RandomEngine.reseedWithDefault()
    link = regina.Link.fromPD(regina_pd(diagram)) if diagram.pd else regina.Link(1)
    if link.countComponents() != 1 or not link.isClassical() or link.writhe() != diagram.writhe():
        raise ValueError('Regina conversion did not preserve the classical knot data')
    link.simplify()
    triangulation = link.complement()
    if (not triangulation.isValid() or not triangulation.isOrientable()
            or triangulation.countBoundaryComponents() != 1):
        raise ValueError('unexpected knot-complement triangulation')
    # isSolidTorus is a complete decision; knowsSolidTorus is NOT a verdict.
    solid_torus = triangulation.isSolidTorus()
    return dict(version=1, engine='regina', engine_version=regina.versionString(),
                distribution_version=version('regina'),
                input_digest=request['input_digest'], input_crossings=diagram.crossings,
                simplified_crossings=link.size(), tetrahedra=triangulation.size(),
                status='UNKNOT' if solid_torus else 'KNOTTED',
                trust='external-engine verdict; no independently checked normal-surface certificate')


def main():
    try:
        result = decide(json.load(sys.stdin))
    except Exception as exc:
        print(json.dumps(dict(error=type(exc).__name__ + ': ' + str(exc))))
        return 1
    print(json.dumps(result))
    return 0


if __name__ == '__main__':
    sys.exit(main())
