"""PL mapping tori and spherical quotients with independently colored edges."""

from collections import Counter, defaultdict, deque
from fractions import Fraction as F
from functools import cache
from itertools import combinations, permutations, product
import json
from math import floor
from pathlib import Path

from sympy import Integer, Matrix, ZZ, cyclotomic_poly
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp


class Hamilton:
    """Exact unit quaternions (a + b j), a,b in Z[exp(pi i/N)].

    Coefficients in the complex plane are reduced by the cyclotomic polynomial.
    Quaternion products use j c = conjugate(c) j and j^2 = -1.
    """

    def __init__(self, n):
        self.n = n
        self.size = 4*n
        self.i, self.j = 1, 2*n
        self.minpoly = tuple(map(int, reversed(cyclotomic_poly(2*n, polys=True).all_coeffs())))
        d = self.degree = len(self.minpoly)-1
        zero, one = (0,)*d, (1,)+(0,)*(d-1)
        powers = [self.reduce([0]*k+[1]) for k in range(2*n)]
        self.zpowers = powers
        self.units = [(a, zero) for a in powers] + [(zero, a) for a in powers]
        index = {q: k for k, q in enumerate(self.units)}
        assert len(index) == self.size and self.units[0] == (one, zero)
        self.table = [[index[self.hamilton_mul(g, h)] for h in self.units]
                      for g in self.units]
        self.inverse = [row.index(0) for row in self.table]
        self.power = cache(self.power)

    def reduce(self, polynomial):
        d = self.degree
        coefficients = list(polynomial) + [0]*max(0, d-len(polynomial))
        for k in range(len(coefficients)-1, d-1, -1):
            for j, coefficient in enumerate(self.minpoly[:-1]):
                coefficients[k-d+j] -= coefficients[k]*coefficient
        return tuple(coefficients[:d])

    def complex_mul(self, a, b):
        coefficients = [0]*(2*self.degree-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                coefficients[i+j] += x*y
        return self.reduce(coefficients)

    def conjugate(self, a):
        return tuple(sum(a[k]*self.zpowers[-k % (2*self.n)][j] for k in range(self.degree))
                     for j in range(self.degree))

    def hamilton_mul(self, g, h):
        a, b = g
        c, d = h
        ac, bd = self.complex_mul(a, c), self.complex_mul(b, self.conjugate(d))
        ad, bc = self.complex_mul(a, d), self.complex_mul(b, self.conjugate(c))
        return tuple(x-y for x, y in zip(ac, bd)), tuple(x+y for x, y in zip(ad, bc))

    def mul(self, a, b):
        return self.table[a][b]

    def quotient(self, a, b):
        return self.mul(self.inverse[a], b)

    def power(self, a, k):
        result = 0
        for _ in range(k % (2*self.n if a < 2*self.n else 4)):
            result = self.mul(result, a)
        return result

    def pair(self, a, b, x, y):
        return self.mul(self.power(a, x), self.power(b, y))

    def omega(self, a, b, c):
        if self.n % 2:
            qa, qb, qc = ((2*(g % (2*self.n)) + (g >= 2*self.n)) % 4 for g in (a, b, c))
            return (qa % 2)*((qb+qc)//4)
        return (a % 2)*(b % 2)*(c >= 2*self.n)


class SmithComparison:
    """Independent comparison via integer linear lifts of the published d_i.

    Each Smith certificate has S*d*T = D. A lift of a cycle is found by
    dividing S times the cycle by the nonzero diagonal, then applying T.
    The same oriented degree-three basis as the published resolution is used.
    """

    def __init__(self, group):
        self.g = group
        n, x, y, size = group.n, group.i, group.j, group.size
        xy = group.mul(x, y)
        columns = [
            [[(0, x, 1), (0, 0, -1)], [(0, y, 1), (0, 0, -1)]],
            [[*((0, k, 1) for k in range(n)), (1, 0, -1), (1, y, -1)],
             [(0, 0, 1), (0, xy, 1), (1, x, 1), (1, 0, -1)]],
            [[(0, x, 1), (0, 0, -1), (1, 0, 1), (1, xy, -1)]],
        ]
        self.lifts = []
        self.matrices = []
        for degree, cells in enumerate(columns):
            shape = ((1, 2, 2)[degree]*size, len(cells)*size)
            differential = Matrix.zeros(*shape)
            for j, column in enumerate(cells):
                for h in range(size):
                    for i, a, c in column:
                        differential[i*size+group.mul(h, a), j*size+h] += c
            d, s, t = (m.to_Matrix() for m in smith_normal_decomp(
                DomainMatrix.from_Matrix(differential).convert_to(ZZ)))
            assert s*differential*t == d
            diag = [int(d[i, i]) for i in range(min(d.shape)) if d[i, i]]
            self.lifts.append((differential, s, t, diag))
            self.matrices.append({"differential": differential.tolist(),
                                  "smith_left": s.tolist(), "smith_right": t.tolist(),
                                  "diagonal": diag})
        self.image = cache(self.image)
        self.weight = cache(self.weight)

    def image(self, simplex):
        size = self.g.size
        if not simplex:
            return (1,) + (0,)*(size-1)
        degree = len(simplex)
        differential, s, t, diag = self.lifts[degree-1]
        if 0 in simplex:
            return (0,)*differential.cols
        a = simplex[0]
        lower = self.image(simplex[1:])
        rhs = [0]*len(lower)
        for index, coefficient in enumerate(lower):
            cell, h = divmod(index, size)
            rhs[cell*size + self.g.mul(a, h)] += coefficient
        for i in range(degree-1):
            face = (*simplex[:i], self.g.mul(*simplex[i:i+2]), *simplex[i+2:])
            sign = (-1)**(i+1)
            rhs = [c+sign*b for c, b in zip(rhs, self.image(face))]
        rhs = Matrix([c+(-1)**degree*b for c, b in zip(rhs, self.image(simplex[:-1]))])
        transformed = list(s*rhs)
        assert all(transformed[i] % d == 0 for i, d in enumerate(diag))
        assert not any(transformed[len(diag):])
        lift = t*Matrix([x//d for x, d in zip(transformed, diag)]
                        + [0]*(t.cols-len(diag)))
        assert differential*lift == rhs
        return tuple(map(int, lift))

    def weight(self, a, b, c):
        return sum(self.image((a, b, c))) % self.g.size


def sign_of(values):
    return (-1)**sum(a > b for a, b in combinations(values, 2))


def cross(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def area2(polygon):
    return sum(a[0]*b[1]-a[1]*b[0] for a, b in zip(polygon, polygon[1:]+polygon[:1]))


def clip(triangle, cutter):
    """Exact oriented convex clipping. Collinear boundary points are retained."""
    polygon = list(triangle)
    for a, b in zip(cutter, cutter[1:]+cutter[:1]):
        new = []
        for p, q in zip(polygon, polygon[1:]+polygon[:1]):
            dp, dq = cross(a, b, p), cross(a, b, q)
            if dp >= 0:
                new.append(p)
            if dp*dq < 0:
                new.append(tuple((dq*x-dp*y)/(dq-dp) for x, y in zip(p, q)))
        polygon = list(dict.fromkeys(new))
        if len(polygon) < 3:
            return []
    return polygon if area2(polygon) > 0 else []


def box(triangle):
    xs, ys = zip(*triangle)
    return min(xs), min(ys), max(xs), max(ys)


def local_shifts(base, other, periodic_y):
    ax, ay, bx, by = box(base)
    cx, cy, dx, dy = box(other)
    xs = range(floor(ax-dx), floor(bx-cx)+1)
    ys = range(floor(ay-dy), floor(by-cy)+1) if periodic_y else (0,)
    for x, y in product(xs, ys):
        if bx > cx+x and dx+x > ax and by > cy+y and dy+y > ay:
            yield x, y


def shift(points, x, y):
    return tuple((a+x, b+y) for a, b in points)


def overlay(base, moved, name, periodic_y):
    """For each coarse triangle, return its exact common subdivision.

    The two projections use translated lifts of precisely the same polygons.
    Every positive-area polygon is triangulated by an interior fan.
    """
    bottom, top = [[] for _ in base], [[] for _ in moved]
    polygons = []

    def vertex(point):
        x, y = point
        return name + (x % 1, y % 1 if periodic_y else y)

    for i, first in enumerate(base):
        for j, second in enumerate(moved):
            for dx, dy in local_shifts(first, second, periodic_y):
                polygon = clip(first, shift(second, dx, dy))
                if not polygon:
                    continue
                # A vertex on a shared collinear edge must occur on both sides.
                for point in (*first, *shift(second, dx, dy)):
                    if point in polygon:
                        continue
                    for k, (a, b) in enumerate(zip(polygon, polygon[1:]+polygon[:1])):
                        if cross(a, b, point) == 0 and all(
                            min(x, y) <= z <= max(x, y) for x, y, z in zip(a, b, point)
                        ):
                            polygon.insert(k+1, point)
                            break
                center = tuple(sum(col)/len(polygon) for col in zip(*polygon))
                polygons.append((i, j, (dx, dy), polygon))
                for a, b in zip(polygon, polygon[1:]+polygon[:1]):
                    fine = (center, a, b)
                    assert area2(fine) > 0
                    keys = tuple(map(vertex, fine))
                    bottom[i].append((keys, fine))
                    top[j].append((keys, shift(fine, -dx, -dy)))
    for coarse, refined in [(base, bottom), (moved, top)]:
        for triangle, children in zip(coarse, refined):
            assert area2(triangle) == sum(area2(points) for _, points in children)
    return bottom, top, polygons


def affine(point, matrix):
    x, y = point
    a, b, c, d = matrix
    return a*x+b*y, c*x+d*y


def strip_surface(n):
    """Two doubled hexagons, with Q at u=1 and P at u=0 on the three collars."""
    names = ("a", "c", "w")
    pants_faces = []
    for side in (0, 1):
        perimeter = []
        for name in names:
            perimeter.extend((("seam", name, side, 0), ("seam", name, side, 2)))
        for sheet in (0, 1):
            outline = []
            for k, (a, b) in enumerate(zip(perimeter, perimeter[1:]+perimeter[:1])):
                outline.append(a)
                if k % 2 == 0:
                    outline.append(("seam", names[k//2], side, 1 if sheet == 0 else 3))
            center = ("pants", side, sheet)
            for a, b in zip(outline, outline[1:]+outline[:1]):
                positive = (side == 1) != (sheet == 1)
                pants_faces.append(((center, a, b) if positive else (center, b, a),
                                    ("pants", side, sheet)))
    strips = []
    for name, shear in (("a", n), ("c", 2), ("w", 2)):
        faces, coords = [], []
        for j in range(4):
            a, b = F(j, 4), F(j+1, 4)
            p, q, r, s = (a, F(0)), (b, F(0)), (b, F(1)), (a, F(1))
            for triangle in ((p, q, r), (p, r, s)):
                faces.append(tuple(("seam", name, int(y), int(4*x) % 4) for x, y in triangle))
                coords.append(triangle)
        strips.append((name, shear, faces, coords))
    return pants_faces, strips


def torus_surface():
    faces, coords = [], []
    for i, j in product(range(3), repeat=2):
        a, b, c, d = ((F(i, 3), F(j, 3)), (F(i+1, 3), F(j, 3)),
                      (F(i+1, 3), F(j+1, 3)), (F(i, 3), F(j+1, 3)))
        for triangle in ((a, b, c), (a, c, d)):
            coords.append(triangle)
            faces.append(tuple(("torus", x % 1, y % 1) for x, y in triangle))
    return faces, coords


def replace_strip_boundary(key):
    name, x, y = key
    if y in (0, 1):
        assert (x*4).denominator == 1
        return ("seam", name, int(y), int(4*x))
    return ("strip", name, x, y)


def make_prisms(surface, matrix=None):
    """Return two overlay halves and a constant final cap.

    A prism record consists of its coarse face, the triangles on the opposite
    side, and the coordinates of both in a single horizontal lift.
    """
    bottom, top, polygons = [], [], {}
    if matrix is None:
        pants, strips = surface
        for face, chart in pants:
            uv = ((F(0), F(0)), (F(1), F(0)), (F(0), F(1)))
            bottom.append((face, uv, [(face, uv)], chart))
            top.append((face, uv, [(face, uv)], chart))
        for name, shear, faces, coords in strips:
            moved = [tuple(affine(p, (1, shear, 0, 1)) for p in tri) for tri in coords]
            low, high, tiles = overlay(coords, moved, (name,), False)
            polygons[name] = tiles
            for result, coarse, fine in ((bottom, coords, low), (top, moved, high)):
                for face, uv, children in zip(faces, coarse, fine):
                    result.append((face, uv, [
                        (tuple(map(replace_strip_boundary, keys)), points)
                        for keys, points in children], ("strip", name)))
    else:
        faces, coords = surface
        moved = [tuple(affine(p, matrix) for p in tri) for tri in coords]
        low, high, tiles = overlay(coords, moved, ("torus",), True)
        polygons["torus"] = tiles
        for result, coarse, fine in ((bottom, coords, low), (top, moved, high)):
            result.extend((face, uv, children, ("torus",))
                          for face, uv, children in zip(faces, coarse, fine))
    final = [(face, uv, [(face, uv)], chart) for face, uv, _, chart in top]
    return (bottom, top, final), polygons


def oriented_side(face, coarse, refined):
    i, j = face
    a, b = coarse[i], coarse[j]
    direction = 0 if a[0] != b[0] else 1
    points = []
    for vertices, coords in refined:
        for key, p in zip(vertices, coords):
            if cross(a, b, p) == 0 and all(
                min(x, y) <= z <= max(x, y) for x, y, z in zip(a, b, p)
            ):
                points.append((key, p))
    values = sorted(set(points), key=lambda pair: pair[1][direction],
                    reverse=a[direction] < b[direction])
    assert values[0][1] == b and values[-1][1] == a
    return values


class Cylinder:
    """An open triangulated product with PL coordinates on its prism charts."""

    def __init__(self, surface, matrix=None):
        self.matrix = matrix
        self.collar_shears = ({name: shear for name, shear, *_ in surface[1]}
                              if matrix is None else None)
        self.prisms, self.overlay_polygons = make_prisms(surface, matrix)
        self.vertices = {}
        self.coordinates = []
        self.tets = []
        self.chart_potentials = {}
        self.outer = [dict(), dict()]
        for index, (records, (lower, upper, sign)) in enumerate(
            zip(self.prisms, ((0, 1, 1), (2, 1, -1), (2, 3, 1)))
        ):
            for record in records:
                self.add_prism(index, lower, upper, sign, record)
        self.cut = self.verify_cut()

    def add_prism(self, index, lower, upper, sign, prism):
        triangle, coords, refined, chart = prism
        chart_id = len(self.chart_potentials)
        local = {}
        self.chart_potentials[chart_id] = (chart, local)

        def vertex(key, uv, layer):
            name = (layer, key)
            if name not in self.vertices:
                self.vertices[name] = len(self.vertices)
                self.coordinates.append(name)
            v = self.vertices[name]
            if v in local:
                assert local[v] == uv
            local[v] = uv
            if layer in (0, 3):
                self.outer[layer == 3][key] = v
            return v

        low = tuple(vertex(v, p, lower) for v, p in zip(triangle, coords))
        high = [tuple(vertex(v, p, upper) for v, p in zip(keys, uv)) for keys, uv in refined]
        middle = tuple(sum(col)/3 for col in zip(*coords))
        center = vertex(("prism", index, *sorted(triangle)), middle, "internal")
        faces = [(low[1], low[0], low[2]), *high]
        for i, j in ((0, 1), (1, 2), (2, 0)):
            side = oriented_side((i, j), coords, refined)
            panel = [low[i], low[j], *(vertex(v, p, upper) for v, p in side)]
            mid = tuple((a+b)/2 for a, b in zip(coords[i], coords[j]))
            cone = vertex(("panel", index, *sorted((triangle[i], triangle[j]))), mid, "internal")
            faces.extend((cone, v, w) for v, w in zip(panel, panel[1:]+panel[:1]))
        for face in faces:
            ordered = (center, *face)
            self.tets.append((tuple(sorted(ordered)), sign*sign_of(ordered), chart_id))

    def verify_cut(self):
        counts = defaultdict(list)
        for vertices, sign, _ in self.tets:
            for i in range(4):
                counts[vertices[:i]+vertices[i+1:]].append(sign*(-1)**i)
        boundary = {face: inc[0] for face, inc in counts.items() if len(inc) == 1}
        assert all(len(inc) == 1 or sorted(inc) == [-1, 1] for inc in counts.values())
        expected = {}
        for endpoint, records in enumerate((self.prisms[0], self.prisms[2])):
            for vertices, *_ in records:
                oriented = tuple(self.outer[endpoint][v] for v in vertices)
                expected[tuple(sorted(oriented))] = (-1 if endpoint == 0 else 1)*sign_of(oriented)
        assert expected == boundary and set(self.outer[0]) == set(self.outer[1])
        coarse = [record[0] for record in self.prisms[0]]
        middle = [face for record in self.prisms[0] for face, _ in record[2]]
        fiber_checks = [verify_surface(layer) for layer in (coarse, middle)]
        assert all(check["genus"] == (2 if self.matrix is None else 1) for check in fiber_checks)
        return {"oriented_cut_boundary": sorted(boundary.items()),
                "gluing": sorted((v, self.outer[1][key]) for key, v in self.outer[0].items()),
                "prism_counts": [len(p) for p in self.prisms],
                "coarse_fiber_triangles": len(coarse), "mid_fiber_triangles": len(middle),
                "coarse_and_mid_fiber_checks": fiber_checks}

    def raw_geometry(self):
        return {"matrix": self.matrix, "collar_shears": self.collar_shears,
                "vertices": self.coordinates,
                "oriented_tetrahedra": self.tets, "cut": self.cut,
                "overlay_polygons": self.overlay_polygons, "prism_coordinates": self.prisms}

    def colors(self, group, pair=None, conjugator=0):
        hamilton = group
        if pair is None:
            hz = {"a": group.i, "c": group.inverse[group.j],
                  "w": group.mul(group.inverse[group.i], group.j)}
            a, c, w = (hz[k] for k in ("a", "c", "w"))
            assert group.mul(group.mul(a, w), c) == 0
            assert all(group.power(hol, self.collar_shears[k]) == group.n for k, hol in hz.items())
            # All three bridge arcs lie in first hexagons and theta=0.
            # On the second hexagon assign constant potentials along sutures.
            p = {"a": (a, 0), "c": (0, group.inverse[c]),
                 "w": (group.inverse[c], a)}
            # Each ordered pair records the values at theta=0 and theta=1/2.
            assert all(group.quotient(odd, even) == hz[k] for k, (even, odd) in p.items())

        def potential(chart, key, pos):
            layer, label = key
            x, y = pos
            if chart[0] == "strip":
                value = group.power(hz[chart[1]], floor(x))
                if layer == 3 and y == 0:
                    value = group.mul(value, group.n)
                return value
            if chart[0] == "pants":
                value = 0
                if chart[2] == 1:
                    seam = label
                    if label[0] == "panel" and all(e[0] == "seam" for e in label[-2:]):
                        # Suture ends have the same potential. On a seam
                        # panel use its lift before the wrap through theta=1.
                        seam = max(label[-2:], key=lambda e: e[3])
                    if seam[0] == "seam":
                        even, odd = p[seam[1]]
                        value = even if seam[3] == 0 else odd
                if layer == 3 and chart[1] == 0:
                    value = group.mul(value, group.n)
                return value
            value = hamilton.pair(*pair, floor(x), floor(y))
            if layer == 3:
                px, py = affine(label[1:], self.matrix)
                base = hamilton.pair(*pair, floor(px), floor(py))
                value = group.mul(group.quotient(base, value), conjugator)
            return value

        lookup = {}
        for chart_id, (chart, local) in self.chart_potentials.items():
            lookup[chart_id] = {vertex: potential(chart, self.coordinates[vertex], pos)
                                for vertex, pos in local.items()}
        colors = {}
        for tet, _, chart_id in self.tets:
            chart = lookup[chart_id]
            for a, b in combinations(tet, 2):
                color = group.quotient(chart[a], chart[b])
                assert colors.setdefault((a, b), color) == color, (a, b, chart_id)
        return colors


EDGE_SLOTS = tuple(combinations(range(4), 2))
FACE_SLOTS = tuple(tuple(j for j in range(4) if j != i) for i in range(4))
EDGE_SLOT = {edge: index for index, edge in enumerate(EDGE_SLOTS)}


def simplex_edges(vertices):
    return tuple(combinations(vertices, 2))


def simplex_faces(vertices):
    return tuple(tuple(vertices[i] for i in slots) for slots in FACE_SLOTS)


def is_connected(graph):
    target = len(graph)
    seen = {next(iter(graph))}
    queue = list(seen)
    for vertex in queue:
        for neighbor in graph[vertex]:
            if neighbor not in seen:
                queue.append(neighbor)
                seen.add(neighbor)
    return len(seen) == target


def verify_surface(triangles):
    incidence = defaultdict(list)
    vertex_links = defaultdict(lambda: defaultdict(list))
    for index, triangle in enumerate(triangles):
        assert len(set(triangle)) == 3
        for a, b in zip(triangle, triangle[1:]+triangle[:1]):
            incidence[tuple(sorted((a, b)))].append((index, 1 if a < b else -1))
        for i, v in enumerate(triangle):
            a, b = triangle[i-1], triangle[(i+1) % 3]
            vertex_links[v][a].append(b)
            vertex_links[v][b].append(a)
    dual = defaultdict(list)
    for sides in incidence.values():
        (a, sign_a), (b, sign_b) = sides
        assert a != b and sign_a == -sign_b
        dual[a].append(b)
        dual[b].append(a)
    assert is_connected(dual)
    for link in vertex_links.values():
        assert all(len(adj) == 2 and adj[0] != adj[1] for adj in link.values())
        assert is_connected(link)
    chi = len(vertex_links)-len(incidence)+len(triangles)
    return {"f_vector": [len(vertex_links), len(incidence), len(triangles)],
            "euler_characteristic": chi, "genus": (2-chi)//2}


def verify_manifold(tets, colors, group, links=True):
    """Verify the ordered Δ-complex, with explicit cell identifiers in each tet."""
    face_sides = defaultdict(list)
    edge_links = defaultdict(lambda: defaultdict(list))
    vertex_links = defaultdict(list)
    dw = Counter()
    face_edges = {}
    for tet_id, (vertices, sign, edges, faces) in enumerate(tets):
        assert len(set(vertices)) == 4
        dw[tuple(colors[edges[EDGE_SLOT[(i, i+1)]]] for i in range(3))] += sign
        for i, slots in enumerate(FACE_SLOTS):
            face = faces[i]
            face_sides[face].append(sign*(-1)**i)
            e01, e02, e12 = (edges[EDGE_SLOT[pair]] for pair in combinations(slots, 2))
            assert face_edges.setdefault(face, (e01, e02, e12)) == (e01, e02, e12)
        if links:
            for (i, j), edge in zip(EDGE_SLOTS, edges):
                f1, f2 = [faces[k] for k in range(4) if k != i and k != j]
                assert f1 != f2
                edge_links[edge][f1].append(f2)
                edge_links[edge][f2].append(f1)
            for i, vertex in enumerate(vertices):
                inc_edges = [e for pair, e in zip(EDGE_SLOTS, edges) if i in pair]
                inc_faces = [(f, sign*(-1)**(i+j-(i < j)))
                             for j, f in enumerate(faces) if i != j]
                vertex_links[vertex].append((tet_id, inc_edges, inc_faces))
    assert all(sorted(inc) == [-1, 1] for inc in face_sides.values())
    assert all(group.mul(colors[a], colors[c]) == colors[b] for a, b, c in face_edges.values())
    result = {"f_vector": [len({v for vertices, *_ in tets for v in vertices}),
                           len(colors), len(face_sides), len(tets)],
              "face_orientation_defects": 0, "flatness_defects": 0,
              "dw_triples": [[triplet, n] for triplet, n in sorted(dw.items()) if n]}
    if links:
        cycles = Counter()
        for link in edge_links.values():
            assert all(len(adj) == 2 and adj[0] != adj[1] for adj in link.values())
            assert is_connected(link)
            cycles[len(link)] += 1
        spheres = Counter()
        for link in vertex_links.values():
            link_vertices = {e for _, edges, _ in link for e in edges}
            link_edges = defaultdict(list)
            for tet_id, _, faces in link:
                for face, sign in faces:
                    link_edges[face].append((tet_id, sign))
            graph = defaultdict(set)
            for incidents in link_edges.values():
                assert len(incidents) == 2
                (i, s_i), (j, s_j) = incidents
                assert i != j and s_i == -s_j
                graph[i].add(j)
                graph[j].add(i)
            assert is_connected(graph)
            assert len(link_vertices)-len(link_edges)+len(link) == 2
            spheres[(len(link_vertices), len(link_edges), len(link))] += 1
        result["edge_link_length_histogram"] = sorted(cycles.items())
        result["vertex_link_f_vector_histogram"] = sorted(spheres.items())
    return result


def assemble(stages):
    """Glue the distinct cut boundaries of a cyclic list of product cylinders."""
    global_ids = {}
    colors = {}
    tets = []
    endpoint_maps = []
    for i, (cylinder, coloring) in enumerate(stages):
        endpoints = {}
        for step, endpoint in enumerate(cylinder.outer):
            for key, v in endpoint.items():
                endpoints[v] = ("fiber", (i+step) % len(stages), key)
        vertices = {}
        for v in range(len(cylinder.coordinates)):
            key = endpoints.get(v, ("interior", i, v))
            vertices[v] = global_ids.setdefault(key, len(global_ids))
        for tet, sign, _ in cylinder.tets:
            ordered = tuple(vertices[v] for v in tet)
            canonical = tuple(sorted(ordered))
            tets.append((canonical, sign*sign_of(ordered),
                         simplex_edges(canonical), simplex_faces(canonical)))
        group = coloring[0]
        for (a, b), color in coloring[1].items():
            u, v = vertices[a], vertices[b]
            if u > v:
                u, v, color = v, u, group.inverse[color]
            assert colors.setdefault((u, v), color) == color
        endpoint_maps.append(vertices)
    return tets, colors, global_ids, endpoint_maps


def path_holonomy(loop, group, colors):
    color = 0
    for a, b in zip(loop, loop[1:]):
        edge_color = colors[(a, b)] if a < b else group.inverse[colors[(b, a)]]
        color = group.mul(color, edge_color)
    return color


def spatial_markings(cylinder, remap, group, colors):
    """Mark based loops via the three bridges from Q to P."""
    q, p = ("pants", 1, 0), ("pants", 0, 0)

    def crossing(name):
        return [q, ("seam", name, 1, 0), ("seam", name, 0, 0), p]

    def circle(name, side, direction=1):
        base = q if side == 1 else p
        return [base, *(("seam", name, side, (direction*k) % 4) for k in range(5)), base]

    def follow(*paths):
        assert all(x[-1] == y[0] for x, y in zip(paths, paths[1:]))
        return [*paths[0], *(v for path in paths[1:] for v in path[1:])]

    a, c, w = (crossing(name) for name in ("a", "c", "w"))
    marking = {
        "a": circle("a", 1),
        "b": follow(w, a[::-1]),
        "c": follow(w, circle("c", 0, -1), w[::-1]),
        "d": follow(c, w[::-1]),
        "w": circle("w", 1),
    }
    loops = {name: [remap[cylinder.vertices[(0, v)]] for v in path]
             for name, path in marking.items()}
    loops["t"] = [remap[cylinder.vertices[(layer, q)]] for layer in range(4)]
    expected = {"a": group.i, "b": 0, "c": group.j, "d": 0,
                "w": group.mul(group.inverse[group.i], group.j), "t": 0}
    result = {}
    for name, loop in loops.items():
        color = path_holonomy(loop, group, colors)
        assert color == expected[name], (name, color, expected[name])
        result[name] = {"vertices": loop, "holonomy": color}
    return result


def torus_markings(cylinder, group, colors):
    x = [("torus", F(k % 3, 3), F(0)) for k in range(4)]
    y = [("torus", F(0), F(k % 3, 3)) for k in range(4)]
    paths = {"a": [(0, key) for key in x], "b": [(0, key) for key in y],
             "t": [(layer, x[0]) for layer in range(4)]}
    result = {}
    for key, path in paths.items():
        path = [cylinder.vertices[vertex] for vertex in path]
        result[key] = {"vertices": path, "holonomy": path_holonomy(path, group, colors)}
    return result


def tree_gauge(colors, group, root):
    """Put the independently constructed bundle in maximal-tree gauge."""
    adjacency = defaultdict(list)
    for (a, b), color in colors.items():
        adjacency[a].append((b, color))
        adjacency[b].append((a, group.inverse[color]))
    gauge = {root: 0}
    tree = []
    queue = deque([root])
    while queue:
        a = queue.popleft()
        for b, color in sorted(adjacency[a]):
            if b not in gauge:
                gauge[b] = group.mul(gauge[a], color)
                tree.append(tuple(sorted((a, b))))
                queue.append(b)
    assert len(gauge) == len(adjacency)
    gauged = {(a, b): group.mul(group.mul(gauge[a], c), group.inverse[gauge[b]])
              for (a, b), c in colors.items()}
    assert all(gauged[e] == 0 for e in tree)
    return gauged, tree


def smith_h1(tets, colors, tree):
    """Contract the cellular spanning tree before Smith reduction of ∂₂."""
    remaining = sorted(set(colors)-set(tree))
    col_id = {edge: i for i, edge in enumerate(remaining)}
    faces = sorted({face for _, _, _, fs in tets for face in fs})
    rows = [{col_id[edge]: sign for edge, sign in
             zip(combinations(face, 2), (1, -1, 1)) if edge in col_id} for face in faces]
    columns = defaultdict(set)
    pending = deque()
    for i, row in enumerate(rows):
        for j, c in row.items():
            columns[j].add(i)
            if abs(c) == 1:
                pending.append((i, j))
    used = set()
    pivots = []
    while pending:
        i, j = pending.popleft()
        pivot = rows[i].get(j, 0)
        if abs(pivot) != 1:
            continue
        used.add(j)
        pivots.append((i, j, pivot))
        row = rows[i]
        for other in sorted(columns[j]-{i}):
            target = rows[other]
            scale = target[j]*pivot
            for k, v in row.items():
                changed = target.get(k, 0)-scale*v
                if changed:
                    columns[k].add(other)
                    target[k] = changed
                    if abs(changed) == 1:
                        pending.append((other, k))
                elif k in target:
                    del target[k]
                    columns[k].remove(other)
        for k in row:
            columns[k].remove(i)
        rows[i] = {}
    free_cols = sorted(set(range(len(remaining)))-used)
    residual = [[row.get(j, 0) for j in free_cols] for row in rows if row]
    diagonal = []
    if residual:
        smith = smith_normal_form(Matrix(residual), domain=ZZ)
        diagonal = [abs(int(smith[i, i])) for i in range(min(smith.shape)) if smith[i, i]]
    return {"presentation_shape": [len(faces), len(remaining)],
            "tree": tree, "unit_pivots": pivots, "remaining_columns": free_cols,
            "residual_matrix": residual, "nonunit_smith_diagonal": [d for d in diagonal if d > 1],
            "free_rank": len(free_cols)-len(diagonal)}


def evaluate(result, cocycle, modulus):
    return sum(sign*cocycle(*triple) for triple, sign in result["dw_triples"]) % modulus


def genus_two_geometry(group, comparison):
    cylinder = Cylinder(strip_surface(group.n))
    tets, colors, ids, (remap,) = assemble([(cylinder, (group, cylinder.colors(group)))])
    ungauged = verify_manifold(tets, colors, group, links=False)
    markings = spatial_markings(cylinder, remap, group, colors)
    colors, tree = tree_gauge(colors, group, markings["t"]["vertices"][0])
    assert spatial_markings(cylinder, remap, group, colors) == markings
    result = verify_manifold(tets, colors, group)
    h1 = smith_h1(tets, colors, tree)
    mod2, raw = evaluate(result, group.omega, 2), evaluate(result, comparison.weight, group.size)
    assert mod2 == evaluate(ungauged, group.omega, 2) == raw % 2 == 1
    assert raw == evaluate(ungauged, comparison.weight, group.size)
    if group.n == 2:
        assert h1["free_rank"] == 3 and h1["nonunit_smith_diagonal"] == [2, 6]
    return {**result, "h1": h1, "mod2": mod2, "raw_periodic_residue": raw,
            "marked_loops": markings, "open_cylinder": cylinder.raw_geometry(),
            "closed_vertices": list(ids), "closed_tetrahedra": [[v, s] for v, s, *_ in tets],
            "open_to_closed_vertices": sorted(remap.items()),
            "edge_colors_in_tree_gauge": [[edge, color] for edge, color in sorted(colors.items())]}


def spherical_quotient(group, deck, cocycle, modulus):
    """Take orbits of flags of the boundary of the four-dimensional cross-polytope."""
    assert group.n == 2
    # Each actual cross-polytope vertex is a signed basis quaternion.
    axes = [(0, 2), (1, 3), (4, 6), (5, 7)]
    inverse_axis = {v: (i, sign) for i, ends in enumerate(axes)
                    for v, sign in zip(ends, (1, -1))}

    @cache
    def translate(flag, a):
        return tuple(tuple(sorted(group.mul(a, v) for v in face)) for face in flag)

    @cache
    def orbit(flag):
        translated = [(translate(flag, a), a) for a in deck]
        assert len({f for f, _ in translated}) == len(deck)
        return min(translated)

    ids = [dict() for _ in range(4)]
    tets, colors, reps = [], {}, []
    for cross_face in product(*axes):
        for ordered in permutations(cross_face):
            flag = tuple(tuple(sorted(ordered[:i])) for i in range(1, 5))
            if orbit(flag)[0] != flag:
                continue
            coordinates, directions = zip(*(inverse_axis[v] for v in ordered))
            sign = sign_of(coordinates)
            for d in directions:
                sign *= d
            simplex_ids = []
            for degree in range(1, 4):
                level = ids[degree-1]
                simplex_ids.append(tuple(level.setdefault(orb, len(level))
                                         for part in combinations(flag, degree)
                                         for orb, _ in (orbit(part),)))
            vertices, edges, faces = simplex_ids
            # Face slots delete a vertex, hence the reverse of combinations.
            tets.append((vertices, sign, edges, faces[::-1]))
            reps.append(flag)
            shifts = [group.inverse[orbit((face,))[1]] for face in flag]
            for edge, (i, j) in zip(edges, EDGE_SLOTS):
                value = group.quotient(shifts[i], shifts[j])
                assert value in deck
                assert colors.setdefault(edge, value) == value
    result = verify_manifold(tets, colors, group)
    assert len(tets)*len(deck) == 16*24
    assert all(table for table in ids[:3])
    return {**result, "deck_group": deck, "tetrahedra": tets, "flag_lifts": reps,
            "cell_orbit_representatives": [list(level) for level in ids[:3]],
            "edge_colors": sorted(colors.items()), "raw_residue": evaluate(result, cocycle, modulus)}


MATRICES = {"S": (0, -1, 1, 0), "T": (1, 1, 0, 1),
            "S^-1": (0, 1, -1, 0), "T^-1": (1, -1, 0, 1),
            "i": (1, 0, 0, 1), "j": (1, 0, 0, 1),
            "i^-1": (1, 0, 0, 1), "j^-1": (1, 0, 0, 1)}


def inverse_name(name):
    return name[:-3] if name.endswith("^-1") else name+"^-1"


def action(group, pair, name):
    a, b, c, d = MATRICES[name]
    acting = group.i if name[0] == "i" else group.j if name[0] == "j" else 0
    if name.endswith("^-1"):
        acting = group.inverse[acting]
    result = group.pair(*pair, a, c), group.pair(*pair, b, d)
    return tuple(group.mul(acting, group.mul(x, group.inverse[acting])) for x in result), acting


def matrix_product(left, right):
    a, b, c, d = left
    e, f, g, h = right
    return a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h


def geometric_torus_regression(group):
    pairs = [(a, b) for a, b in product(range(group.size), repeat=2)
             if group.mul(a, b) == group.mul(b, a)]
    edges = [(pair, name, action(group, pair, name)[0])
             for pair in pairs for name in ("S", "T", "i", "j")]
    adjacency = defaultdict(list)
    for i, (a, name, b) in enumerate(edges):
        adjacency[a].append((i, name, b))
        adjacency[b].append((i, inverse_name(name), a))
    root_paths, orbits, tree = {}, [], set()
    for pair in pairs:
        if pair in root_paths:
            continue
        root_paths[pair] = (pair, [])
        orbit = [pair]
        for a in orbit:
            for edge, name, b in adjacency[a]:
                if b not in root_paths:
                    tree.add(edge)
                    orbit.append(b)
                    root_paths[b] = (pair, [*root_paths[a][1], name])
        orbits.append(orbit)

    @cache
    def template(matrix):
        return Cylinder(torus_surface(), matrix)

    stage_evidence = {}

    @cache
    def stage(pair, name):
        target, gauge = action(group, pair, name)
        cylinder = template(MATRICES[name])
        colors = cylinder.colors(group, pair, group.inverse[gauge])
        markings = torus_markings(cylinder, group, colors)
        assert [markings[k]["holonomy"] for k in ("a", "b", "t")] == [*pair, group.inverse[gauge]]
        index = len(stage_evidence)
        stage_evidence[(pair, name)] = {
            "index": index, "source": pair, "target": target, "generator": name,
            "marked_paths": markings,
            "open_edge_colors": "".join(str(colors[edge]) for edge in sorted(colors)),
        }
        return target, (cylinder, (group, colors))

    loops = []
    for edge_id, (a, name, b) in enumerate(edges):
        if edge_id in tree:
            continue
        root, start = root_paths[a]
        assert root == root_paths[b][0]
        circuit = [*start, name, *(inverse_name(e) for e in reversed(root_paths[b][1]))]
        current = root
        stages, pairs_along, stages_used = [], [root], []
        matrix, time = (1, 0, 0, 1), 0
        for generator in circuit:
            current, colored = stage(current, generator)
            evidence = stage_evidence[(pairs_along[-1], generator)]
            stages_used.append(evidence["index"])
            matrix = matrix_product(matrix, MATRICES[generator])
            time = group.mul(time, evidence["marked_paths"]["t"]["holonomy"])
            stages.append(colored)
            pairs_along.append(current)
        assert current == root
        tets, colors, _, _ = assemble(stages)
        verification = verify_manifold(tets, colors, group)
        mod2 = evaluate(verification, group.omega, 2)
        assert mod2 == 0
        loops.append({"edge_id": edge_id, "root": root, "word": circuit,
                      "pairs_along": pairs_along, "stage_indices": stages_used,
                      "matrix": matrix, "time_holonomy": time,
                      "mod2": mod2, **verification})
    template_keys = {name: name if name[0] in "ST" else "i" for name in MATRICES}
    templates = {}
    for name in sorted(set(template_keys.values())):
        cylinder = template(MATRICES[name])
        edge_order = sorted({edge for tet, _, _ in cylinder.tets for edge in simplex_edges(tet)})
        templates[name] = {**cylinder.raw_geometry(), "open_edge_order": edge_order}
    return {"commuting_pairs": pairs, "edges": edges, "orbits": orbits,
            "tree_edges": sorted(tree), "loops": loops, "templates": templates,
            "template_for_generator": template_keys, "colored_stages": list(stage_evidence.values())}


def odd_torus_geometry(group, comparison):
    cylinder = Cylinder(torus_surface(), (1, 4, 0, 1))
    colors = cylinder.colors(group, (group.j, 0))
    markings = torus_markings(cylinder, group, colors)
    assert [markings[k]["holonomy"] for k in ("a", "b", "t")] == [group.j, 0, 0]
    tets, colors, ids, (remap,) = assemble([(cylinder, (group, colors))])
    tree_colors, tree = tree_gauge(colors, group, remap[markings["t"]["vertices"][0]])
    result = verify_manifold(tets, colors, group)
    assert verify_manifold(tets, tree_colors, group, links=False)["flatness_defects"] == 0
    h1 = smith_h1(tets, colors, tree)
    assert h1["free_rank"] == 2 and h1["nonunit_smith_diagonal"] == [4]
    mod2 = evaluate(result, group.omega, 2)
    raw = evaluate(result, comparison.weight, group.size)
    assert mod2 == raw % 2 == 1
    return {**result, "mod2": mod2, "raw_periodic_residue": raw,
            "h1": h1, "open_marked_paths": markings,
            "open_cylinder": cylinder.raw_geometry(),
            "open_to_closed_vertices": sorted(remap.items()),
            "closed_vertices": list(ids),
            "closed_tetrahedra": [[v, s] for v, s, *_ in tets],
            "edge_colors": sorted(colors.items())}


def build_certificates():
    q8 = Hamilton(2)
    comparison = SmithComparison(q8)
    deck = list(range(4))
    cyclic = spherical_quotient(q8, deck, lambda a, b, c: a*((b+c)//4), 4)
    assert cyclic["raw_residue"] in (1, 3)
    orientation = 1 if cyclic["raw_residue"] == 1 else -1
    cyclic["orientation_multiplier"] = orientation
    cyclic["calibrated_mod4"] = cyclic["raw_residue"]*orientation % 4
    cyclic["calibrated_root_of_unity"] = "+i"
    sphere = spherical_quotient(q8, range(8), comparison.weight, 8)
    sphere["mod2"] = evaluate(sphere, q8.omega, 2)
    sphere["calibrated_mod8"] = orientation*sphere["raw_residue"] % 8
    assert sphere["f_vector"][-1] == 48
    assert sphere["mod2"] == 1 and sphere["calibrated_mod8"] in (1, 7)
    samples = {}
    for n in (2, 3, 4, 6):
        group = q8 if n == 2 else Hamilton(n)
        cochain = comparison if n == 2 else SmithComparison(group)
        result = (genus_two_geometry(group, cochain) if n % 2 == 0
                  else odd_torus_geometry(group, cochain))
        result["calibrated_periodic_residue"] = orientation*result["raw_periodic_residue"] % group.size
        samples[str(n)] = result
    histogram = Counter((comparison.weight(b, c, d) - comparison.weight(q8.mul(a, b), c, d)
                         + comparison.weight(a, q8.mul(b, c), d)
                         - comparison.weight(a, b, q8.mul(c, d))
                         + comparison.weight(a, b, c)) % 8
                        for a, b, c, d in product(range(8), repeat=4))
    assert histogram == {0: 4096}
    table = [[[comparison.weight(a, b, c) for c in range(8)]
              for b in range(8)] for a in range(8)]
    assert all(table[a][b][c] == 0 for a, b, c in product(range(8), repeat=3) if 0 in (a, b, c))
    return {"samples": samples, "lens": cyclic, "spherical_q8": sphere,
            "comparison_smith_q8": comparison.matrices,
            "w8_table": table, "w8_coboundary_histogram": dict(histogram),
            "torus_regression": geometric_torus_regression(q8)}


def json_value(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, range):
        return list(value)
    if isinstance(value, Integer):
        return int(value)
    raise TypeError(type(value).__name__)


def main():
    certificate = build_certificates()
    output = Path(__file__).resolve().parents[1] / "certificates/path_b_certificates.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(certificate, separators=(",", ":"), default=json_value) + "\n")
    print({n: {k: s[k] for k in ("f_vector", "mod2", "raw_periodic_residue",
                                "calibrated_periodic_residue")}
           for n, s in certificate["samples"].items()})
    print("lens", certificate["lens"]["raw_residue"], "sphere", certificate["spherical_q8"]["raw_residue"])
    loops = certificate["torus_regression"]
    print(f'{len(loops["orbits"])} orbits, {len(loops["loops"])} geometric stabilizer loops')


if __name__ == "__main__":
    main()
