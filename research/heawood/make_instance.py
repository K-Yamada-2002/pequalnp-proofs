"""Prepare an exact search on the incidences of a selected set of Fano points."""
import sys
from itertools import combinations, permutations
from restrict import EDGES, normalize, vertices


def automorphisms():
    lines = [frozenset(a for a,b in EDGES if b == i) for i in range(7,14)]
    for perm in permutations(range(7)):
        image = [frozenset(perm[i] for i in line) for line in lines]
        if all(line in lines for line in image):
            yield list(perm) + [lines.index(line)+7 for line in image]


def classify():
    group = list(automorphisms())
    print("point automorphisms",len(group))
    # Put the seven line neighborhoods into the same triple system as the points.
    lines = {frozenset(a for a,b in EDGES if b==i):i for i in range(7,14)}
    for perm in permutations(range(7)):
        dual_triples = [frozenset(perm[b-7] for a,b in EDGES if a==i) for i in range(7)]
        if all(t in lines for t in dual_triples):
            dual = [lines[t] for t in dual_triples] + list(perm)
            assert {(dual[b],dual[a]) for a,b in EDGES} == set(EDGES)
            print("point-line duality",dual)
            break
    else:
        raise ValueError("no duality found")
    for k in range(1,8):
        remaining = set(combinations(range(7),k))
        while remaining:
            rep = min(remaining)
            orbit = {tuple(sorted(g[i] for i in rep)) for g in group}
            if not orbit <= remaining:
                raise ValueError("overlapping orbits")
            remaining -= orbit
            print("".join(map(str,rep)),len(orbit))


def emit(points, budget):
    mask = normalize(sum(1 << p for p in points) | (127 << 7))
    vs = vertices(mask)
    edges = [(vs.index(a), vs.index(b)) for a,b in EDGES if a in vs and b in vs]
    group = []
    for relabel in automorphisms():
        if {relabel[i] for i in points} == set(points):
            group.append([vs.index(relabel[i]) for i in vs])
    starts = []
    for i,j in combinations(range(len(vs)),2):
        if (i,j) != min(tuple(sorted((g[i],g[j]))) for g in group):
            continue
        for op in ('and','or'):
            starts.append((i,j,int(op=='or')))
    print(len(vs),len(edges),budget,len(starts))
    for a,b in edges:
        print(a,b)
    for row in starts:
        print(*row)


if __name__ == '__main__':
    if sys.argv[1:] == ["--orbits"]:
        classify()
    else:
        emit([int(i) for i in sys.argv[1]], int(sys.argv[2]))
