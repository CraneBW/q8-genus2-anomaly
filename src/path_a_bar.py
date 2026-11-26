"""Normalized integral bar chains and periodic-resolution comparison maps."""

from collections import Counter, deque
from functools import cache
from itertools import product
import json
from pathlib import Path


IDENTITY = 0
RELATOR = (1, 2, -1, -2, 3, 4, -3, -4)


def terms(chain):
    return [[list(basis), coefficient] for basis, coefficient in sorted(chain.items())
            if coefficient]


def chain_of(items):
    chain = Counter()
    for basis, coefficient in items:
        chain[basis] += coefficient
    return Counter({basis: c for basis, c in chain.items() if c})


def boundaries(basis, multiply):
    yield basis[1:], 1
    for i in range(len(basis) - 1):
        yield (*basis[:i], multiply(*basis[i:i+2]), *basis[i+2:]), (-1)**(i+1)
    yield basis[:-1], (-1)**len(basis)


def boundary(chain, multiply, unit):
    return chain_of((face, coefficient * sign)
                    for basis, coefficient in chain.items()
                    for face, sign in boundaries(basis, multiply) if unit not in face)


def pairing(chain, cocycle):
    return sum(coefficient * cocycle(*basis) for basis, coefficient in chain.items())


class Dicyclic:
    def __init__(self, n):
        self.n = n
        self.size = 4*n
        self.r, self.s = 1, 2*n
        self.table = tuple(tuple(self.multiply(g, h) for h in range(self.size))
                           for g in range(self.size))
        self.inverse = tuple(row.index(0) for row in self.table)

    def multiply(self, g, h):
        n = self.n
        q, p = divmod(g, 2*n)
        v, u = divmod(h, 2*n)
        return (p + (-1)**q*u + n*q*v) % (2*n) + 2*n*(q ^ v)

    def mul(self, g, h):
        return self.table[g][h]

    def pow(self, g, exponent):
        if exponent < 0:
            g, exponent = self.inverse[g], -exponent
        result = IDENTITY
        for _ in range(exponent):
            result = self.mul(result, g)
        return result

    def xy(self, g):
        half, rotation = divmod(g, 2*self.n)
        return rotation % 2, half

    def abelianization4(self, g):
        half, rotation = divmod(g, 2*self.n)
        return (2*rotation + half) % 4

    def omega(self, g, h, k):
        if self.n % 2:
            a, b, c = map(self.abelianization4, (g, h, k))
            return (a % 2) * ((b+c)//4)
        return self.xy(g)[0] * self.xy(h)[0] * self.xy(k)[1]

    def generator(self):
        r, s = self.r, self.s
        rs = self.mul(r, s)
        return chain_of([*(((r, j, r), 1) for j in range(1, self.n)),
                         ((r, s, s), -1), ((rs, rs, r), -1), ((rs, r, s), -1)])


class PeriodicComparison:
    """Tomoda–Zvengrowski Props. 3.2–3.3, with group-ring coefficients on the left.

    Free chain terms are (left coefficient, cell index). The homotopy is
    Z-linear; the resulting F is extended ZG-linearly.
    """

    def __init__(self, group):
        self.group = group
        n, x, y = group.n, group.r, group.s
        xy = group.mul(x, y)
        self.differentials = (
            (), ({(x, 0): 1, (0, 0): -1}, {(y, 0): 1, (0, 0): -1}),
            ({**{(i, 0): 1 for i in range(n)}, (y, 1): -1, (0, 1): -1},
             {(xy, 0): 1, (0, 0): 1, (x, 1): 1, (0, 1): -1}),
            ({(x, 0): 1, (0, 0): -1, (0, 1): 1, (xy, 1): -1},),
            ({(g, 0): 1 for g in range(group.size)},),
        )
        self.s_tables = tuple(tuple(tuple(self.homotopy(degree, g, cell)
                                         for cell in range(rank))
                                    for g in range(group.size))
                              for degree, rank in enumerate((1, 2, 2, 1)))
        self.compare = cache(self.compare)
        self.verify_homotopy()

    def homotopy(self, degree, g, cell):
        group = self.group
        n, y = group.n, group.s
        y2, y3 = group.pow(y, 2), group.pow(y, 3)
        half, rotation = divmod(g, 2*n)
        i, j = rotation % n, 2*(rotation//n) + half
        xy = group.mul(1, y)

        def polynomial(items):
            return chain_of(((coefficient, c), sign) for coefficient, c, sign in items)

        def shifted(g, elements, c, sign=1):
            return [(group.mul(g, e), c, sign) for e in elements]

        if degree == 0:
            return polynomial(shifted(0, range(i), 0)
                              + shifted(i, [group.pow(y, k) for k in range(j)], 1))
        if degree == 1:
            if cell == 1:
                items = (shifted(i, [y, 0], 0, -1)
                         + shifted(group.mul(i, y), range(n), 1)) if j == 3 else []
            elif j == 0:
                items = [(0, 0, 1)] if i == n-1 else []
            elif j == 1 and i == 0:
                items = [(n-1, 0, 1), (0, 0, -1), (group.mul(n-1, y), 0, 1),
                         (y, 1, 1)] + shifted(group.mul(n-1, y), range(n), 1, -1)
            elif j == 1:
                items = [(i-1, 1, 1)]
            elif j == 2 and i < n-1:
                items = [(i+1, 0, 1), (i, 0, -1)]
            elif j == 2:
                items = [(y, 0, -1), (y3, 1, 1), (n-1, 1, -1)] + shifted(y, range(n), 1)
            elif i == 0:
                items = [(0, 0, -1), (n-1, 1, 1)]
            else:
                items = shifted(i-1, [0, y2], 1) + shifted(i-1, [xy], 1, -1)
            return polynomial(items)
        if degree == 2:
            if j == 0:
                items = []
            elif cell == 0 and j == 1:
                items = [(group.mul(k+i+1, y), 0, 1) for k in range(n-i-1)]
                items += shifted(0, range(n-1), 0, -1)
            elif cell == 0 and j == 2:
                items = shifted(n-1, range(i+1), 0)
                items += [(group.mul(k, xy), 0, 1) for k in range(i)]
            elif cell == 0:
                items = [(group.mul(i+1+k, y3), 0, 1) for k in range(n)]
                items += shifted(0, range(i), 0, -1)
            elif j == 1:
                items = [(i-1, 0, -1)] if i else []
            elif j == 2 and i < n-1:
                items = [(i, 0, -1)]
            elif j == 2:
                items = [(n-1, 0, 1)] + [(group.mul(k, y2), 0, 1) for k in range(n)]
                items += [(group.mul(k, xy), 0, 1) for k in range(n-1)]
            else:
                items = shifted(i-1, [xy], 0) + shifted(i-1, [0], 0, -1) if i else []
            return polynomial(items)
        return Counter({(0, 0): 1}) if g == y3 else Counter()

    def differential(self, degree, chain):
        return chain_of(((self.group.mul(g, h), target), coefficient * sign)
                        for (g, cell), coefficient in chain.items()
                        for (h, target), sign in self.differentials[degree][cell].items())

    def contract(self, degree, chain):
        return chain_of((basis, coefficient * sign)
                        for (g, cell), coefficient in chain.items()
                        for basis, sign in self.s_tables[degree][g][cell].items())

    def verify_homotopy(self):
        for degree, columns in enumerate(self.differentials[2:], start=2):
            for column in columns:
                assert not self.differential(degree-1, column)
        for degree, table in enumerate(self.s_tables):
            for g, columns in enumerate(table):
                for cell, image in enumerate(columns):
                    unit = Counter({(g, cell): 1})
                    lower = (self.contract(degree-1, self.differential(degree, unit))
                             if degree else Counter({(0, 0): 1}))
                    combined = chain_of((*self.differential(degree+1, image).items(),
                                         *lower.items()))
                    assert combined == unit, (degree, g, cell, combined)

    def compare(self, basis):
        if not basis:
            return Counter({(0, 0): 1})
        if 0 in basis:
            return Counter()
        differential = list(boundaries(basis, self.group.mul))
        free_boundary = chain_of(
            ((self.group.mul(basis[0] if i == 0 else 0, g), cell), sign*coefficient)
            for i, (face, sign) in enumerate(differential)
            for (g, cell), coefficient in self.compare(face).items())
        return self.contract(len(basis)-1, free_boundary)

    def weight(self, *basis):
        return sum(self.compare(basis).values()) % self.group.size


def cocycle_certificate(group, cocycle, modulus):
    zero = all(cocycle(*args) == 0 for args in product(range(group.size), repeat=3)
               if 0 in args)
    residues = Counter(sum(sign*cocycle(*face)
                           for face, sign in boundaries(args, group.mul)) % modulus
                       for args in product(range(group.size), repeat=4))
    assert zero and residues == {0: group.size**4}, residues
    return {"normalized": zero, "coboundary_histogram": dict(residues)}


def comparison_cochain(group, weight):
    """Row-reduce δv = weight - omega over F₂ using exact bit vectors."""
    pairs = list(product(range(1, group.size), repeat=2))
    index = {pair: i for i, pair in enumerate(pairs)}
    rhs = 1 << len(pairs)
    pivots = {}
    for basis in product(range(group.size), repeat=3):
        row = rhs * ((weight(*basis) - group.omega(*basis)) % 2)
        for face, _ in boundaries(basis, group.mul):
            if 0 not in face:
                row ^= 1 << index[face]
        while row & (rhs-1):
            pivot = (row & -row).bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
        else:
            assert row == 0
    solution = 0
    for pivot, row in sorted(pivots.items(), reverse=True):
        bit = bool(row & rhs) ^ bool((row & solution).bit_count() % 2)
        solution |= int(bit) << pivot
    support = {pair for i, pair in enumerate(pairs) if solution & (1 << i)}
    assert all((sum(s*(f in support) for f, s in boundaries(b, group.mul))
                - weight(*b) + group.omega(*b)) % 2 == 0
               for b in product(range(group.size), repeat=3))
    return sorted(support)


def reduce_word(word):
    reduced = []
    for letter in word:
        if reduced and reduced[-1] == -letter:
            reduced.pop()
        else:
            reduced.append(letter)
    return tuple(reduced)


def concatenate(u, v):
    return reduce_word((*u, *v))


def inverse_word(word):
    return tuple(-letter for letter in reversed(word))


def substitute(word, images):
    return reduce_word(letter for x in word
                       for letter in (images[x-1] if x > 0 else inverse_word(images[-x-1])))


def dehn_twists():
    a, b, c, d = (1,), (2,), (3,), (4,)
    w = (2, -1, -2, 3)
    wi = inverse_word(w)
    return ((a, b+a, c, d), (a+(-2,), b, c, d), (a, wi+b, wi+c+w, d+w),
            (a, b, c+(-4,), d), (a, b, c, d+c))


def compose(images, twists):
    for twist in twists:
        images = tuple(substitute(w, twist) for w in images)
    return images


def surface_chain(relator):
    return chain_of([
        *((((relator[:j], (letter,)), 1) for j, letter in enumerate(relator) if j)),
        *(((((word,), (-word,)), -1) for word in relator if word < 0)),
    ])


def tree_filler(basis):
    """K₂ after tensoring the Cayley-tree comparison with the trivial module.

    The oriented tree edge at a negative letter starts at the *next* prefix.
    Applying the homogeneous bar cone to the left translate of those edges
    gives this formula, with the ZG coefficient retained until the cone.
    """
    g, h = basis
    for j, letter in enumerate(h):
        prefix = h[:j] if letter > 0 else h[:j+1]
        if g and prefix:
            yield (g, prefix, (abs(letter),)), 1 if letter > 0 else -1


def conjugation_prism(chain, conjugator, group):
    """∂P_h(C) = C - Ad_h(C) for a 2-cycle C."""
    def conjugate(g):
        return group.mul(group.mul(conjugator, g), group.inverse[conjugator])

    return chain_of((basis, coefficient * sign)
                    for (g, k), coefficient in chain.items()
                    for basis, sign in [((conjugator, g, k), 1),
                                        ((conjugate(g), conjugator, k), -1),
                                        ((conjugate(g), conjugate(k), conjugator), 1)]
                    if 0 not in basis)


@cache
def free_mapping_chain(relator, images):
    assert substitute(relator, images) == relator
    surface = surface_chain(relator)
    assert boundary(surface, concatenate, ()) == Counter({(relator,): -1})
    moved = chain_of((tuple(substitute(w, images) for w in basis), c)
                     for basis, c in surface.items())
    difference = chain_of((*moved.items(), *((b, -s) for b, s in surface.items())))
    filler = chain_of((basis, c * sign) for pair, c in difference.items()
                      for basis, sign in tree_filler(pair))
    assert boundary(filler, concatenate, ()) == difference
    return surface, difference, filler


def mapping_bar(relator, images, holonomies, time, group, record=True):
    @cache
    def eval_word(word):
        value = 0
        for letter in word:
            g = holonomies[abs(letter)-1]
            value = group.mul(value, g if letter > 0 else group.inverse[g])
        return value

    assert eval_word(relator) == 0
    assert tuple(eval_word(word) for word in images) == tuple(
        group.mul(group.mul(time, g), group.inverse[time]) for g in holonomies)
    surface, difference, filler = free_mapping_chain(relator, images)

    def push(chain):
        return chain_of((image, c) for basis, c in chain.items()
                        if 0 not in (image := tuple(map(eval_word, basis))))

    prism = conjugation_prism(push(surface), time, group)
    pushed_difference = push(difference)
    assert boundary(prism, group.mul, 0) == Counter({b: -c for b, c in pushed_difference.items()})
    result = chain_of((*push(filler).items(), *prism.items()))
    assert boundary(result, group.mul, 0) == Counter()
    if not record:
        return result
    return result, {"surface": terms(surface), "free_difference": terms(difference),
                    "free_filler": terms(filler), "prism": terms(prism),
                    "fiber_holonomies": list(holonomies), "time_holonomy": time,
                    "images": images, "relator": relator, "cycle": terms(result)}


def genus_two(group):
    t1, _, t3, _, t5 = dehn_twists()
    images = compose(((1,), (2,), (3,), (4,)), [t5]*2 + [t3]*2 + [t1]*group.n)
    return mapping_bar(RELATOR, images, (group.r, 0, group.s, 0), 0, group)


def torus_twist(group, holonomy, times):
    return mapping_bar((1, 2, -1, -2), ((1,), (2,) + (1,)*times),
                       (holonomy, 0), 0, group)


def half_difference(matrix, first, second, group):
    a, b, c, d = matrix
    x0, y0 = group.xy(first)
    x1, y1 = group.xy(second)
    delta_a, delta_b = (a-1)*x0 + c*x1, b*x0 + (d-1)*x1
    assert delta_a % 2 == delta_b % 2 == 0
    return ((delta_a//2)*y1 - (delta_b//2)*y0) % 2


def torus_free_lifts():
    """Find integral lifts in the two oriented torus Dehn twists and inverses."""
    identity = ((1,), (2,))
    moves = (((1,), (2, 1)), ((1,), (2, -1)),
             ((1, -2), (2,)), ((1, 2), (2,)))
    lifts = {(1, 0, 0, 1): identity}
    queue = deque([identity])
    while queue:
        current = queue.popleft()
        for twist in moves:
            first, second = images = tuple(substitute(word, twist) for word in current)
            a, b, c, d = (word.count(letter)-word.count(-letter)
                          for letter in (1, 2) for word in (first, second))
            key = tuple(x % 4 for x in (a, b, c, d))
            if key not in lifts:
                assert a*d-b*c == 1
                lifts[key] = images
                queue.append(images)
    return lifts


def torus_regression(group):
    """Wang/Bockstein pairing for integer lifts of the two fiber characters.

    x² restricts to zero on the fiber. Its Wang representative is
    (M*X-X)/2; the time component of x has integral lift, and cancels
    in the square. Pair this representative with y on the oriented
    fiber. Lifts of M modulo 4 leave this expression modulo 2 fixed.
    """
    matrices = [m for m in product(range(4), repeat=4) if (m[0]*m[3]-m[1]*m[2]) % 4 == 1]
    pairs = [(g, h) for g, h in product(range(group.size), repeat=2)
             if group.mul(g, h) == group.mul(h, g)]
    lifts = torus_free_lifts()
    assert set(lifts) == set(matrices)
    valid, bar_cycles = [], []
    for i, matrix in enumerate(matrices):
        a, b, c, d = matrix
        for j, (g, k) in enumerate(pairs):
            acted = (group.mul(group.pow(g, a), group.pow(k, c)),
                     group.mul(group.pow(g, b), group.pow(k, d)))
            for time in range(group.size):
                conjugated = tuple(group.mul(group.mul(time, x), group.inverse[time])
                                   for x in (g, k))
                if acted == conjugated:
                    parity = half_difference(matrix, g, k, group)
                    cycle = mapping_bar((1, 2, -1, -2), lifts[matrix], (g, k), time,
                                        group, record=False)
                    assert parity == pairing(cycle, group.omega) % 2 == 0
                    valid.append([i, j, time, parity])
                    bar_cycles.append(terms(cycle))
    return {"matrices": matrices, "commuting_pairs": pairs, "time_elements": list(range(group.size)),
            "candidate_count": len(matrices)*len(pairs)*group.size, "valid": valid,
            "free_group_lifts": [lifts[m] for m in matrices], "bar_cycles_for_valid": bar_cycles}


def cyclic_weight(size, a, b, c):
    return a*((b+c)//size)


def lens_certificate():
    # The standard cyclic cellular lens cycle with positively oriented 3-cell.
    cycl = chain_of(((1, j, 1), 1) for j in range(1, 4))
    assert not boundary(cycl, lambda a, b: (a+b) % 4, 0)
    residue = pairing(cycl, lambda *args: cyclic_weight(4, *args)) % 4
    assert residue == 1
    return {"lens": "L(4,1)", "cycle": terms(cycl), "mod4": residue,
            "root_of_unity": "+i"}


def build_certificates():
    twists = dehn_twists()
    twist_images = [substitute(RELATOR, t) for t in twists]
    assert twist_images == [RELATOR]*5
    samples = {}
    for n in (2, 3, 4, 6):
        group = Dicyclic(n)
        comparison = PeriodicComparison(group)
        d = group.generator()
        assert not boundary(d, group.mul, 0)
        cycle, cert = genus_two(group) if n % 2 == 0 else torus_twist(group, group.s, 4)
        cert["mod2"] = pairing(cycle, group.omega) % 2
        cert["periodic_residue"] = pairing(cycle, comparison.weight) % group.size
        cert["term_count"] = len(cycle)
        assert cert["mod2"] == cert["periodic_residue"] % 2 == 1
        generator_value = pairing(d, comparison.weight) % group.size
        assert generator_value in (1, group.size-1)
        extra = {}
        if n == 2:
            extra = {
                "multiplication_table": group.table,
                "w8_table": [[[comparison.weight(a, b, c) for c in range(8)]
                              for b in range(8)] for a in range(8)],
                "v_support": comparison_cochain(group, comparison.weight),
                "v_coboundary_triples_checked": 8**3,
                "periodic_differentials": [list(map(terms, degree)) for degree in comparison.differentials],
                "periodic_homotopy": [[[terms(c) for c in columns] for columns in degree]
                                      for degree in comparison.s_tables],
            }
        if n == 3:
            c6, c6_cert = torus_twist(group, group.r, 6)
            c6_value = pairing(c6, comparison.weight) % group.size
            assert c6_value in (2, 10) and cert["periodic_residue"] in (3, 9)
            extra["cyclic_order_6_torus"] = {**c6_cert, "periodic_residue": c6_value}
        samples[str(n)] = {"order": group.size, "cocycle": cocycle_certificate(group, group.omega, 2),
                           "periodic_cocycle": cocycle_certificate(group, comparison.weight, group.size),
                           "generator": terms(d), "generator_mod2": pairing(d, group.omega) % 2,
                           "generator_periodic_residue": generator_value, "mapping_torus": cert,
                           **extra}
    group = Dicyclic(2)
    # Conjugation by j fixes -1 and takes i to i(-1), as does one torus twist.
    twisted, general = mapping_bar((1, 2, -1, -2), ((1,), (2, 1)),
                                   (group.pow(group.r, 2), group.r), group.s, group)
    assert twisted and general["prism"]
    return {"orientation_convention": "fiber followed by positive time",
            "twists": twists, "relator_images": twist_images, "samples": samples,
            "torus_regression": torus_regression(group), "lens": lens_certificate(),
            "nontrivial_conjugation_prism": general}


def main():
    certificate = build_certificates()
    output = Path(__file__).resolve().parents[1] / "certificates/path_a_certificates.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
    print({n: {k: s["mapping_torus"][k] for k in ("term_count", "mod2", "periodic_residue")}
           for n, s in certificate["samples"].items()})
    print(f'{len(certificate["torus_regression"]["valid"])} valid torus configurations')


if __name__ == "__main__":
    main()
