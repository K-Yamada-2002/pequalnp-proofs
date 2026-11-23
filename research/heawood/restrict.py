"""Lower bounds for the Heawood graph via restrictions at the first binary gate."""
from functools import lru_cache
from itertools import combinations, product

EDGES = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
         (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
         (6,8),(6,9),(6,11)]
N = [sum(1 << (a+b-v) for a,b in EDGES if v in (a,b)) for v in range(14)]
FULL = (1 << 14) - 1


def vertices(mask):
    return [i for i in range(14) if mask & 1 << i]


@lru_cache(None)
def normalize(mask):
    return sum(1 << v for v in vertices(mask) if N[v] & mask)


def exact_easy(mask):
    # L104 covers forests. L532 covers degree-at-most-two graphs here:
    # an induced component with edges is a path or a cycle of length >= 6.
    vs = vertices(mask)
    seen = 0
    components = 0
    for v in vs:
        if seen & 1 << v:
            continue
        components += 1
        todo = 1 << v
        while todo:
            seen |= todo
            neighbors = 0
            for i in vertices(todo):
                neighbors |= N[i]
            todo = neighbors & mask & ~seen
    degrees = [(N[v] & mask).bit_count() for v in vs]
    e = sum(degrees) // 2
    if e != len(vs) - components and max(degrees) > 2:
        return None
    # Enumerate the chosen cover vertices on the seven-point side.
    # Every neighbor of an unchosen point is forced on the other side.
    points = mask & 127
    chosen = points
    cover = len(vs)
    while True:
        lines = 0
        for v in vertices(points ^ chosen):
            lines |= N[v] & mask
        cover = min(cover, chosen.bit_count() + lines.bit_count())
        if not chosen:
            break
        chosen = (chosen-1) & points
    return e + cover - 1


@lru_cache(None)
def lower(mask):
    mask0 = normalize(mask)
    if mask != mask0:
        return lower(mask0)
    if not mask:
        return 0
    vs = vertices(mask)
    if len(vs) == 2:
        return 1
    seed = exact_easy(mask)
    if seed is not None:
        return seed
    base = max(len(vs) - 1, max(1 + lower(mask ^ (1 << v)) for v in vs))
    # Complete incidence blocks have the separately checked bounds below.
    # Point-line duality is verified by make_instance.py --orbits.
    for side in (127, 127 << 7):
        centers = vertices(mask & side)
        if 1 <= len(centers) <= 5 and all(N[v] & mask == N[v] for v in centers):
            base = max(base, min(4 * len(centers) - 1, 18))
    minimum = 10 ** 3
    for u,v in combinations(vs, 2):
        for op in ('and','or'):
            minimum = min(minimum, first(mask, u, v, op)[0])
    return max(minimum, base)


def cofactor(mask, zero, one):
    # Adjacent true vertices already force the constant true.
    neighbors = 0
    for i in vertices(one):
        neighbors |= N[i]
    if neighbors & one:
        return 0
    rest = mask & ~(zero | one)
    singles = neighbors & rest
    residual = normalize(rest & ~singles)
    # The singleton variables are essential and setting them to zero
    # one at a time eliminates at least one gate if a residual edge remains.
    return lower(residual) + singles.bit_count() if residual else max(0, singles.bit_count()-1)


def first(mask, u, v, op):
    U,V = 1 << u,1 << v
    nu,nv = N[u]&mask, N[v]&mask
    if op == 'and':
        extra_u, extra_v = bool(nu & ~V), bool(nv & ~U)
    else:
        extra_u, extra_v = bool(nu & ~nv), bool(nv & ~nu)
    twins = nu & ~V == nv & ~U
    best = 0
    choice = ()
    for a,b in product((-1,0,1),repeat=2):  # -1 leaves a variable free.
        if a == b == -1:
            continue
        one = (U if a==1 else 0) | (V if b==1 else 0)
        zero = (U if a==0 else 0) | (V if b==0 else 0)
        # A minimum normalized circuit has no reader of the first gate
        # whose other operand is u or v, by idempotence and absorption.
        constant_gate = a == b or (0 if op=='and' else 1) in (a,b)
        extra = int((a != -1 and extra_u) or (b != -1 and extra_v))
        if a != -1 and b != -1 and extra_u and extra_v and not twins:
            extra = 2
        score = 1 + extra + int(constant_gate) + cofactor(mask,zero,one)
        if score > best:
            best,choice = score,(a,b)
    return best,choice


if __name__ == '__main__':
    from collections import Counter
    print('Heawood lower bound', lower(FULL))
    for op in ('and','or'):
        print(op, sorted(Counter(first(FULL,u,v,op)[0] for u,v in combinations(range(14),2)).items()))
