#!/usr/bin/env python3
"""Render extremal Platonic shadows from the exact certificate's vertex data.

Dependencies: numpy, scipy, matplotlib.  Run from any working directory:
    python3 code/draw_shadows.py

Outputs vector PDF and PNG galleries plus a numeric independent area check.
The exact model coordinates and extremizing directions come from exact_verify;
this script independently orthogonally projects the *vertices*, takes their
2D convex hull, and computes its shoelace area.  The figures and numerical
checks are illustrations, not replacements for the exact certificates.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

import numpy as np
from scipy.spatial import ConvexHull
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, FancyBboxPatch
from exact_verify import MODELS

PROJECT = Path(__file__).resolve().parents[1]
COLORS = {'min': '#137D86', 'max': '#B65D35'}
FILLS = {'min': '#D6EAEB', 'max': '#F2DFD3'}
INK = '#20373D'
MUTED = '#66767B'
SHAPES = {
    'tetrahedron': ('Isosceles triangle', 'Square'),
    'cube': ('Square', 'Regular hexagon'),
    'octahedron': ('Rhombus', 'Square'),
    'dodecahedron': ('Centrally symmetric hexagon', 'Regular decagon'),
    'icosahedron': ('Centrally symmetric hexagon', 'Regular hexagon'),
}
DIRECTIONS = {
    'tetrahedron': (r'(1,1,0)', r'(1,0,0)'),
    'cube': (r'(1,0,0)', r'(1,1,1)'),
    'octahedron': (r'(1,1,0)', r'(1,0,0)'),
    'dodecahedron': (r'(1,0,0)', r'(1,\varphi,0)'),
    'icosahedron': (r'(1,1,0)', r'(1,1,1)'),
}


def project_model(name: str, extremum: str) -> dict:
    model = MODELS[name]
    # Raw edge squared is certified exactly in the companion checker.
    vertices = np.array([[float(k) for k in v] for v in model['v']], dtype=float)
    vertices /= np.sqrt(float(model['e2']))
    direction = np.array([float(k) for k in model['u' + extremum]], dtype=float)
    direction /= np.linalg.norm(direction)
    # Choose a stable orthonormal screen basis by an axis least parallel to u.
    seed = np.eye(3)[np.argmin(np.abs(direction))]
    screen_x = np.cross(seed, direction)
    screen_x /= np.linalg.norm(screen_x)
    screen_y = np.cross(direction, screen_x)
    projected = vertices @ np.stack([screen_x, screen_y], axis=1)
    hull = ConvexHull(projected)
    polygon = projected[hull.vertices]
    # A screen rotation gives the regular hexagons a horizontal long diagonal.
    # It changes neither the viewing direction nor the area.
    if SHAPES[name][extremum == 'max'] == 'Regular hexagon':
        j = int(np.argmax(polygon[:, 0]))
        angle = -np.arctan2(polygon[j, 1], polygon[j, 0])
        rotation = np.array([[np.cos(angle), -np.sin(angle)],
                             [np.sin(angle), np.cos(angle)]])
        projected = projected @ rotation.T
        polygon = polygon @ rotation.T
    # A separate shoelace implementation verifies the hull package's area.
    shoelace = abs(float(np.sum(polygon[:, 0] * np.roll(polygon[:, 1], -1)
                                 - polygon[:, 1] * np.roll(polygon[:, 0], -1)))) / 2
    exact_evaluated = float(model['c']) * np.sqrt(float(model['lo' if extremum == 'min' else 'hi']))
    tolerance = 5e-13 * max(1., exact_evaluated)
    assert abs(shoelace - exact_evaluated) < tolerance, (name, extremum, shoelace, exact_evaluated)
    assert abs(shoelace - hull.volume) < tolerance
    return {'name': name, 'extremum': extremum, 'vertices': projected,
            'polygon': polygon, 'direction': direction,
            'shoelace_area': shoelace, 'convex_hull_area': float(hull.volume),
            'formula_area': exact_evaluated,
            'absolute_error': abs(shoelace - exact_evaluated),
            'tolerance': tolerance, 'hull_vertex_count': len(polygon)}


def render_gallery(names: list[str], results: dict, destination: Path,
                   basename: str, title: str) -> None:
    rows = len(names)
    fig = plt.figure(figsize=(8.8, 1.20 + 2.46 * rows), facecolor='white')
    height = fig.get_figheight()
    fig.text(.045, 1 - .20 / height, title, va='top', fontsize=19, weight='bold', color=INK)
    fig.text(.045, 1 - .57 / height,
             'Orthographic shadows · unit edge length · equal scale within each solid',
             va='top', fontsize=10.4, color=MUTED)
    grid = fig.add_gridspec(rows, 2, left=.04, right=.96,
                           top=1 - .96 / height,
                           bottom=.43 / height, wspace=.065, hspace=.075)
    for row, name in enumerate(names):
        pair = [results[(name, which)] for which in ('min', 'max')]
        radius = max(float(np.abs(item['polygon']).max()) for item in pair)
        for col, (which, item) in enumerate(zip(('min', 'max'), pair)):
            ax = fig.add_subplot(grid[row, col])
            ax.set_axis_off()
            card = FancyBboxPatch((0, 0), 1, 1,
                boxstyle='round,pad=0.00,rounding_size=0.025',
                edgecolor='#E1E8E9', facecolor='#FCFDFD', linewidth=.75,
                transform=ax.transAxes, zorder=-2)
            ax.add_patch(card)
            ax.text(.045, .947, name.capitalize(), va='top', fontsize=12.1,
                    weight='bold', color=INK, transform=ax.transAxes)
            ax.text(.955, .942, 'MINIMUM' if which == 'min' else 'MAXIMUM',
                    va='top', ha='right', fontsize=8.6, weight='bold',
                    color=COLORS[which], transform=ax.transAxes)
            ax.text(.045, .827, SHAPES[name][col], va='top', fontsize=9.4,
                    color=MUTED, transform=ax.transAxes)
            drawing = ax.inset_axes([.05, .205, .9, .56])
            drawing.set_aspect('equal')
            drawing.set_xlim(-1.09 * radius, 1.09 * radius)
            drawing.set_ylim(-1.09 * radius, 1.09 * radius)
            drawing.set_axis_off()
            drawing.add_patch(Polygon(item['polygon'], closed=True,
                              facecolor=FILLS[which], edgecolor=COLORS[which],
                              linewidth=1.7, joinstyle='round'))
            # Vertex marks identify the silhouette's actual polygon vertices.
            drawing.scatter(item['polygon'][:, 0], item['polygon'][:, 1],
                            s=8, color=COLORS[which], zorder=3, linewidths=0)
            ax.text(.045, .105, r'$u\parallel ' + DIRECTIONS[name][col] + '$',
                    va='center', fontsize=10.8, color=INK, transform=ax.transAxes)
            ax.text(.955, .105, r'$A \approx ' + f"{item['formula_area']:.6f}" + '$',
                    va='center', ha='right', fontsize=11.6,
                    weight='bold', color=COLORS[which], transform=ax.transAxes)
    fig.text(.045, .13 / height,
             r'$u$ is normal to the screen; coordinates are those of the report. '
             r'$\varphi=(1+\sqrt{5})/2$.',
             fontsize=8.6, color=MUTED, va='bottom')
    metadata = {'Title': title,
                'Subject': 'Exact-coordinate orthographic projections of Platonic solids',
                'Creator': 'draw_shadows.py / matplotlib'}
    fig.savefig(destination / (basename + '.pdf'), metadata=metadata)
    fig.savefig(destination / (basename + '.png'), dpi=220)
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=PROJECT / 'figures')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({'font.family': 'DejaVu Sans',
        'mathtext.fontset': 'dejavusans', 'pdf.fonttype': 42,
        'ps.fonttype': 42, 'svg.fonttype': 'none'})
    results = {(name, which): project_model(name, which)
               for name in MODELS for which in ('min', 'max')}
    render_gallery(list(MODELS), results, args.output,
                   'extremal_shadows', 'The ten extremal Platonic shadows')
    render_gallery(['tetrahedron', 'cube', 'octahedron'], results, args.output,
                   'simple_shadows', 'Tetrahedron, cube, and octahedron')
    render_gallery(['dodecahedron', 'icosahedron'], results, args.output,
                   'golden_shadows', 'Dodecahedron and icosahedron')
    checks = []
    for item in results.values():
        check = {key: value for key, value in item.items()
                 if key not in ('vertices', 'polygon', 'direction')}
        check['unit_screen_normal'] = item['direction'].tolist()
        check['screen_hull_vertices'] = item['polygon'].tolist()
        checks.append(check)
        print(f"{item['name']:13s} {item['extremum']:3s}: "
              f"{item['hull_vertex_count']:2d} vertices; "
              f"shoelace={item['shoelace_area']:.15g}; "
              f"formula={item['formula_area']:.15g}; "
              f"error={item['absolute_error']:.3g}")
    report = {'status': 'all ten independent convex-hull/shoelace checks passed',
              'purpose': 'Numerical illustration QA; the proof uses exact_verify.py certificates.',
              'unit_edge_length': 1, 'checks': checks}
    (args.output / 'shadow_area_check.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Wrote six figure files and shadow_area_check.json to', args.output)


if __name__ == '__main__':
    main()
