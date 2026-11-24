"""Combine accepted one-NOT shards with exact synthesis on at most four essential inputs."""
import argparse
from collections import Counter
from functools import cache
from itertools import combinations, permutations
from pathlib import Path
import re
import subprocess

BASE = '203efb4b463a58b4e677b3c6f554ddca5ad0e4ab'
SHARDS = [1417, 1419, 1421, 1423, 1425, 1429, 1431, 1433, 1435, 1437, 1439, 1441, 1445, 1447, 1449]


@cache
def monotone(n):
    if not n:
        return (0, 1)
    # The two restrictions are monotone, and the low one is pointwise <= the high one.
    return tuple(low | (high << (1 << (n-1))) for low in monotone(n-1)
                 for high in monotone(n-1) if low & ~high == 0)


def relevant(table, n):
    return [i for i in range(n) if any(((table >> x) ^ (table >> (x ^ (1 << i)))) & 1
                                       for x in range(1 << n))]


def change_inputs(table, mapping):
    return sum(((table >> old) & 1) << x for x, old in enumerate(mapping))


@cache
def reorderings(n):
    return [[sum(((x >> p[i]) & 1) << i for i in range(n)) for x in range(1 << n)]
            for p in permutations(range(n))]


def orbit(table, n):
    last = (1 << n) - 1
    dual = sum((1 - ((table >> (last-x)) & 1)) << x for x in range(last+1))
    return {change_inputs(t, p) for t in (table, dual) for p in reorderings(n)}


def solve(target, n, size, free_inversions):
    modulus = (1 << (1 << n)) - 1
    inputs = tuple(sum(((x >> i) & 1) << x for x in range(1 << n)) for i in range(n))
    positives = [x for x in range(1 << n) if target >> x & 1]
    negatives = [x for x in range(1 << n) if not (target >> x & 1)]
    examples = [(x, y) for x in positives for y in negatives]
    full = (1 << len(examples)) - 1

    @cache
    def separates(wire):
        return sum((((wire >> x) ^ (wire >> y)) & 1) << j for j, (x, y) in enumerate(examples))

    @cache
    def visit(live, left):
        if target in live:
            return ()
        if left == 0 or len(live) > left+1:
            return None
        mask = 0
        for wire in live:
            mask |= separates(wire)
        if mask != full:
            return None
        for a, b in combinations(live, 2):
            rest = tuple(w for w in live if w != a and w != b)
            options = [('and', a & b), ('or', a | b)]
            if free_inversions:
                options.extend([('left', a & (modulus ^ b)), ('right', (modulus ^ a) & b)])
            for op, new in options:
                if new == 0 or new in live:
                    continue
                for keep in ((), (a,), (b,), (a,b)):
                    if 1 + len(rest) + len(keep) > left:
                        continue
                    tail = visit(tuple(sorted((*rest,*keep,new))), left-1)
                    if tail is not None:
                        return ((op, a, b, new), *tail)
        return None

    witness = visit(tuple(sorted(inputs)), size)
    if witness is not None and not free_inversions:
        available = set(inputs)
        for op, a, b, new in witness:
            assert a in available and b in available
            assert new == (a & b if op == 'and' else a | b)
            available.add(new)
        assert target in available and len(witness) <= size
    visit.cache_clear()
    separates.cache_clear()
    return witness


def main(repo):
    tables = set(monotone(5))
    active = {t for t in tables if len(relevant(t, 5)) == 5}
    if not __debug__:
        raise RuntimeError('Run without -O so that every verification assertion executes.')
    covered = set()
    common_statement = None
    for shard in SHARDS:
        name = f'L_meta_{shard}'
        path = f'lean/PEqualNP/Outside/{name}.lean'
        source = subprocess.check_output(
            ['git', '-C', str(repo), 'show', f'{BASE}:{path}'], text=True
        )
        marker = f'theorem PEqualNP.Outside.{name} :'
        assert source.count(marker) == 1
        statement, proof_start, _ = source.split(marker)[1].partition(':=')
        assert proof_start
        table_literal = r'0x[a-f0-9]{8}\b'
        reps = [int(t, 16) for t in re.findall(table_literal, statement)]
        assert len(reps) == len(set(reps)) == 10 and all(t in active for t in reps)
        normalized = ''.join(re.sub(table_literal, 'TABLE', statement).split())
        if common_statement is None:
            common_statement = normalized
        assert normalized == common_statement, name
        for t in reps:
            covered.update(orbit(t, 5))
    assert covered == active and len(active) == 6894
    print('Accepted shards cover all',len(active),'fully dependent functions',flush=True)

    orbits = {}
    frequencies = Counter()
    for t in sorted(tables - active):
        variables = relevant(t, 5)
        n = len(variables)
        if n == 0:
            frequencies[n] += 1
            continue
        projected = change_inputs(t, [sum(((x >> i) & 1) << j for i,j in enumerate(variables))
                                     for x in range(1 << n)])
        rep = min(orbit(projected, n))
        if (n, rep) not in orbits:
            for size in range(n-1, 16):
                if solve(rep, n, size, False) is not None:
                    break
            else:
                raise RuntimeError(f'no monotone construction for {rep:x}')
            if size > 0:
                assert solve(rep, n, size-1, True) is None, (n, rep, size)
            orbits[n,rep] = size
            print(f'{n} inputs, table {rep:x}, optimum {size}',flush=True)
        frequencies[n] += 1
    assert frequencies == {0: 2, 1: 5, 2: 20, 3: 90, 4: 570}
    assert len(orbits) == 16 and len(tables) == 7581
    print('At most four essential inputs:',sorted(frequencies.items()))
    print('Nonconstant reduced orbits:',len(orbits))
    print('Total labelled monotone functions:',len(tables))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repo',type=Path,help='checkout of brilliant-hq/pequalnp-proofs containing the pinned commit')
    main(parser.parse_args().repo)
