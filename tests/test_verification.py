"""Replay the two certificates and compare their independently computed invariants."""

from collections import Counter
from itertools import product
import json
from pathlib import Path
from types import SimpleNamespace

import pytest
from sympy import ZZ
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp

from src import path_a_bar as algebra
from src import path_b_triangulation as geometry


ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture(scope="module")
def a_certificate():
    raw = json.loads((ROOT / "certificates/path_a_certificates.json").read_text())
    assert raw == json.loads(json.dumps(algebra.build_certificates()))
    return raw


@pytest.fixture(scope="module")
def b_certificate():
    raw = json.loads((ROOT / "certificates/path_b_certificates.json").read_text())
    generated = geometry.build_certificates()
    assert raw == json.loads(json.dumps(generated, default=geometry.json_value))
    return raw


def chain_from_json(terms):
    return Counter({tuple(word): sign for word, sign in terms})


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def test_q8_table_and_normalized_order_eight_cocycle(a_certificate):
    data = a_certificate["samples"]["2"]
    multiplication = ("01234567", "12305674", "23016745", "30127456",
                      "47652103", "54763210", "65470321", "76541032")
    assert ["".join(map(str, row)) for row in data["multiplication_table"]] == list(multiplication)
    assert data["periodic_cocycle"] == {"normalized": True, "coboundary_histogram": {"0": 4096}}
    assert data["cocycle"] == data["periodic_cocycle"]
    d = chain_from_json(data["generator"])
    assert d == {(1, 1, 1): 1, (1, 4, 4): -1, (5, 5, 1): -1, (5, 1, 4): -1}
    q8 = algebra.Dicyclic(2)
    assert algebra.boundary(d, q8.mul, 0) == {}
    weight = lambda a, b, c: data["w8_table"][a][b][c]
    assert algebra.pairing(d, weight) % 8 == 1
    support = set(map(tuple, data["v_support"]))
    assert len(support) == 18 and data["v_coboundary_triples_checked"] == 512
    for triple in product(range(8), repeat=3):
        delta = sum(sign*(face in support) for face, sign in algebra.boundaries(triple, q8.mul))
        assert (weight(*triple)-q8.omega(*triple)-delta) % 2 == 0


def test_cayley_tree_chain_and_general_conjugation_prism(a_certificate):
    data = a_certificate["samples"]["2"]["mapping_torus"]
    assert [tuple(t) for t in a_certificate["relator_images"]] == [algebra.RELATOR]*5
    free = Counter({freeze(word): sign for word, sign in data["free_filler"]})
    difference = Counter({freeze(word): sign for word, sign in data["free_difference"]})
    assert algebra.boundary(free, algebra.concatenate, ()) == difference
    group = algebra.Dicyclic(2)
    assert algebra.boundary(chain_from_json(data["cycle"]), group.mul, 0) == {}
    general = a_certificate["nontrivial_conjugation_prism"]
    assert general["time_holonomy"] == 4 and general["prism"]
    assert algebra.boundary(chain_from_json(general["cycle"]), group.mul, 0) == {}

    # All commuting fibers and all possible gauge elements exercise P_h.
    for a, b in a_certificate["torus_regression"]["commuting_pairs"]:
        surface = algebra.chain_of((f, sign) for f, sign in [((a,b),1), ((b,a),-1)] if 0 not in f)
        for h in range(8):
            def conjugate(g):
                return group.mul(group.mul(h, g), group.inverse[h])
            expected = algebra.chain_of(
                (*surface.items(), *((tuple(map(conjugate, f)), -c)
                                     for f, c in surface.items())))
            prism = algebra.conjugation_prism(surface, h, group)
            assert algebra.boundary(prism, group.mul, 0) == expected


@pytest.mark.parametrize("n,bar_terms,tetrahedra,residue", [
    (2, 18, 6744, 3), (3, 3, 2196, 3), (4, 20, 8280, 5), (6, 22, 9816, 7),
])
def test_mapping_tori_agree_after_orientation_calibration(
    a_certificate, b_certificate, n, bar_terms, tetrahedra, residue,
):
    a = a_certificate["samples"][str(n)]
    b = b_certificate["samples"][str(n)]
    witness = a["mapping_torus"]
    assert witness["mod2"] == b["mod2"] == a["generator_mod2"] == 1
    assert len(witness["cycle"]) == witness["term_count"] == bar_terms
    assert b["f_vector"][-1] == tetrahedra
    assert witness["periodic_residue"] == b["calibrated_periodic_residue"] == residue
    assert b["face_orientation_defects"] == b["flatness_defects"] == 0
    assert sum(count for _, count in b["edge_link_length_histogram"]) == b["f_vector"][1]
    assert sum(count for _, count in b["vertex_link_f_vector_histogram"]) == b["f_vector"][0]
    assert all(v-e+f == 2 for (v,e,f), _ in b["vertex_link_f_vector_histogram"])
    genus = 1 if n == 3 else 2
    assert all(surface["genus"] == genus
               for surface in b["open_cylinder"]["cut"]["coarse_and_mid_fiber_checks"])
    assert a["cocycle"]["coboundary_histogram"] == {"0": (4*n)**4}
    assert a["periodic_cocycle"]["coboundary_histogram"] == {"0": (4*n)**4}
    if n == 3:
        assert {"a": 6, "b": 0, "t": 0} == {
            name: path["holonomy"] for name, path in b["open_marked_paths"].items()}
        assert a["cyclic_order_6_torus"]["periodic_residue"] in (2, 10)
        assert b["open_cylinder"]["matrix"] == [1, 4, 0, 1]
        assert b["h1"]["free_rank"] == 2 and b["h1"]["nonunit_smith_diagonal"] == [4]
    else:
        assert b["open_cylinder"]["collar_shears"] == {"a": n, "w": 2, "c": 2}
        assert [b["marked_loops"][name]["holonomy"] for name in "abcdt"] == [1, 0, 2*n, 0, 0]


def test_q8_raw_cut_flatness_and_smith_replay(b_certificate):
    q8 = geometry.Hamilton(2)
    b = b_certificate["samples"]["2"]
    assert b["f_vector"] == [1254, 7998, 13488, 6744]
    assert b["h1"]["free_rank"] == 3
    assert b["h1"]["nonunit_smith_diagonal"] == [2, 6]
    assert b["open_cylinder"]["cut"]["prism_counts"] == [60, 60, 60]
    remap = dict(b["open_to_closed_vertices"])
    for low, high in b["open_cylinder"]["cut"]["gluing"]:
        assert remap[low] == remap[high]
    quotient = Counter()
    for vertices, sign, _ in b["open_cylinder"]["oriented_tetrahedra"]:
        ordered = tuple(remap[v] for v in vertices)
        quotient[(tuple(sorted(ordered)), geometry.sign_of(ordered)*sign)] += 1
    assert quotient == Counter((tuple(v), s) for v, s in b["closed_tetrahedra"])
    colors = {tuple(edge): c for edge, c in b["edge_colors_in_tree_gauge"]}
    tets = [(v, s, geometry.simplex_edges(v), geometry.simplex_faces(v))
            for v, s in map(freeze, b["closed_tetrahedra"])]
    cert = geometry.verify_manifold(tets, colors, q8)
    assert cert["f_vector"] == b["f_vector"]
    smith = geometry.smith_h1(tets, colors, list(map(tuple, b["h1"]["tree"])))
    assert json.loads(json.dumps(smith)) == b["h1"]
    v, s, e, f = tets[0]
    with pytest.raises(AssertionError):
        geometry.verify_manifold([(v, -s, e, f), *tets[1:]], colors, q8)


def test_non_real_lens_and_spherical_calibration(a_certificate, b_certificate):
    a, b = a_certificate["lens"], b_certificate["lens"]
    assert a["mod4"] == b["raw_residue"] == b["calibrated_mod4"] == 1
    assert a["root_of_unity"] == b["calibrated_root_of_unity"] == "+i"
    assert b["orientation_multiplier"] == 1
    assert (-b["raw_residue"]) % 4 == 3
    assert b["f_vector"] == [20, 116, 192, 96]
    q8 = b_certificate["spherical_q8"]
    assert q8["f_vector"] == [10, 58, 96, 48]
    assert q8["mod2"] == 1 and q8["calibrated_mod8"] == 1
    for quotient in (b, q8):
        assert quotient["face_orientation_defects"] == quotient["flatness_defects"] == 0
        assert sum(n for _, n in quotient["edge_link_length_histogram"]) == quotient["f_vector"][1]
        assert all(v-e+f == 2 for (v,e,f), _ in quotient["vertex_link_f_vector_histogram"])


def test_independent_w8_comparison_is_an_explicit_coboundary(a_certificate, b_certificate):
    """Solve δu = W_B-W_A modulo eight without comparing code or group tables."""
    assert b_certificate["w8_coboundary_histogram"] == {"0": 4096}
    first = a_certificate["samples"]["2"]["w8_table"]
    second = b_certificate["w8_table"]
    assert first != second
    pairs = {pair: i for i, pair in enumerate(product(range(1, 8), repeat=2))}
    group = algebra.Dicyclic(2)
    matrix, rhs = [], []
    for a, b, c in product(range(1, 8), repeat=3):
        row = [0]*len(pairs)
        for face, sign in algebra.boundaries((a,b,c), group.mul):
            if face in pairs:
                row[pairs[face]] += sign
        matrix.append(row)
        rhs.append([second[a][b][c]-first[a][b][c]])
    operator = DomainMatrix.from_list(matrix, ZZ)
    d, p, q = (m.to_Matrix() for m in smith_normal_decomp(operator))
    values = list(p*DomainMatrix.from_list(rhs, ZZ).to_Matrix())
    # Each nonzero Smith diagonal entry can be solved as a congruence mod 8.
    smith_indeterminates = []
    for i in range(q.cols):
        smith_indeterminates.append(next(x for x in range(8) if (d[i,i]*x-values[i]) % 8 == 0))
    assert all(x % 8 == 0 for x in values[q.cols:])
    solution = q*DomainMatrix.from_list([[x] for x in smith_indeterminates], ZZ).to_Matrix()
    u = {face: int(solution[i]) % 8 for face, i in pairs.items()}
    for a, b, c in product(range(8), repeat=3):
        delta = sum(sign*u.get(face, 0) for face, sign in algebra.boundaries((a,b,c), group.mul))
        assert (second[a][b][c]-first[a][b][c]-delta) % 8 == 0


def test_q8_full_torus_regression_and_all_geometric_stabilizers(a_certificate, b_certificate):
    data = a_certificate["torus_regression"]
    assert [len(data[key]) for key in ("matrices", "commuting_pairs", "time_elements")] == [48, 40, 8]
    assert data["candidate_count"] == 15360 and len(data["valid"]) == 1920
    pairs = list(map(tuple, data["commuting_pairs"]))
    matrices = list(map(tuple, data["matrices"]))
    valid = {(matrices[i], pairs[j], h): mod2 for i, j, h, mod2 in data["valid"]}
    assert len(valid) == 1920 and set(valid.values()) == {0}
    algebraic_q8 = algebra.Dicyclic(2)
    assert len(data["free_group_lifts"]) == len(matrices)
    for images in data["free_group_lifts"]:
        assert algebra.substitute((1, 2, -1, -2), images) == (1, 2, -1, -2)
    assert len(data["bar_cycles_for_valid"]) == len(valid)
    for entry, (_, _, _, mod2) in zip(data["bar_cycles_for_valid"], data["valid"], strict=True):
        cycle = chain_from_json(entry)
        assert algebra.boundary(cycle, algebraic_q8.mul, 0) == {}
        assert algebra.pairing(cycle, algebraic_q8.omega) % 2 == mod2
    b = b_certificate["torus_regression"]
    assert sorted(map(len, b["orbits"])) == [1, 3, 12, 12, 12]
    assert set(tuple(pair) for orbit in b["orbits"] for pair in orbit) == set(pairs)
    assert len(b["edges"]) == 160 and len(b["tree_edges"]) == 35
    edges = sorted(set(range(160))-set(b["tree_edges"]))
    assert [loop["edge_id"] for loop in b["loops"]] == edges and len(edges) == 125
    templates = {}
    group = geometry.Hamilton(2)
    for name, template in b["templates"].items():
        vertices = list(map(freeze, template["vertices"]))
        outer = [{key: i for i, (layer, key) in enumerate(vertices) if layer == end}
                 for end in (0, 3)]
        templates[name] = SimpleNamespace(coordinates=vertices, outer=outer,
                                          tets=list(map(freeze, template["oriented_tetrahedra"])))
    stages = []
    for stage in b["colored_stages"]:
        name = b["template_for_generator"][stage["generator"]]
        order = map(tuple, b["templates"][name]["open_edge_order"])
        colors = dict(zip(order, map(int, stage["open_edge_colors"]), strict=True))
        for path in stage["marked_paths"].values():
            assert geometry.path_holonomy(path["vertices"], group, colors) == path["holonomy"]
        stages.append((templates[name], (group, colors)))
    for loop in b["loops"]:
        key = (tuple(x % 4 for x in loop["matrix"]), tuple(loop["root"]), loop["time_holonomy"])
        assert valid[key] == loop["mod2"] == 0
        selected = [stages[i] for i in loop["stage_indices"]]
        tets, colors, _, _ = geometry.assemble(selected)
        replay = geometry.verify_manifold(tets, colors, group, links=False)
        assert replay["f_vector"] == loop["f_vector"]
        assert json.loads(json.dumps(replay["dw_triples"])) == loop["dw_triples"]
        assert geometry.evaluate(replay, group.omega, 2) == 0
