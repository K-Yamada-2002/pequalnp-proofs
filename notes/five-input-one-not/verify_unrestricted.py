"""Find exact circuit sizes on five labelled inputs with free wire inversions."""
import argparse
from collections import Counter
from pathlib import Path
import subprocess
import sys

from all_five import change_inputs, monotone, orbit, relevant, solve


def run_search(executable, target, budget, mode, n=5):
    return subprocess.check_output(
        [str(executable), f'{target:08x}', str(budget), mode, str(n)], text=True
    ).split()


def monotone_witness(executable, target):
    # A five-essential-input function needs >= 4 binary gates. The limit only
    # bounds the search for a construction. Failure raises an error.
    for size in range(4, 11):
        result = run_search(executable, target, size, 'monotone')
        if result != ['UNSAT']:
            assert result[0] == 'SAT' and len(result[1:]) == size
            return result[1:]
    raise RuntimeError(f'No construction found for {target:08x}')


def replay(target, gates):
    for x in range(32):
        values = [bool(x & (1 << i)) for i in range(5)]
        for entry in gates:
            operation, first, second = entry.split(',')
            a, b = int(first), int(second)
            assert 0 <= a < b < len(values) and operation in ('A', 'O')
            values.append((values[a] and values[b]) if operation == 'A' else (values[a] or values[b]))
        assert values[-1] == bool(target & (1 << x))


def smaller_optima(tables, executable):
    sizes = {}
    histogram = Counter()
    for table in tables:
        essential = relevant(table, 5)
        n = len(essential)
        if n == 0:
            # The official model reads a missing output as false; true needs an empty AND.
            histogram[int(table != 0)] += 1
            continue
        mapping = [sum(((x >> i) & 1) << j for i, j in enumerate(essential)) for x in range(1 << n)]
        rep = min(orbit(change_inputs(table, mapping), n))
        if (n, rep) not in sizes:
            for size in range(n - 1, 11):
                if solve(rep, n, size, False) is not None:
                    if size:
                        assert solve(rep, n, size - 1, True) is None
                        # Duplicate the smaller truth table across the unused coordinates.
                        expanded = change_inputs(rep, [x % (1 << n) for x in range(32)])
                        assert run_search(executable, expanded, size-1, 'signed', n) == ['UNSAT']
                    sizes[n, rep] = size
                    break
            else:
                raise RuntimeError(f'No smaller construction found for {n} inputs, {rep:x}')
        histogram[sizes[n, rep]] += 1
    assert len(sizes) == 16 and sum(histogram.values()) == 687
    return histogram


def main(executable, cross_check):
    tables = set(monotone(5))
    fully_dependent = {t for t in tables if len(relevant(t, 5)) == 5}
    remaining = fully_dependent.copy()
    labelled = smaller_optima(tables - fully_dependent, executable)
    representatives = 0
    while remaining:
        rep = min(remaining)
        members = orbit(rep, 5)
        assert members <= remaining
        remaining -= members
        gates = monotone_witness(executable, rep)
        replay(rep, gates)
        budget = len(gates) - 1
        result = run_search(executable, rep, budget, 'signed')
        if result != ['UNSAT']:
            raise AssertionError(f'Signed lower bound failed for {rep:08x}: {result}')
        if cross_check:
            assert solve(rep, 5, budget, True) is None, (rep, budget)
        representatives += 1
        labelled[len(gates)] += len(members)
        print(f'{rep:08x} {len(members):3} {len(gates):2}  ' + ' '.join(gates), flush=True)
    assert representatives == 95 and len(fully_dependent) == 6894
    assert sum(labelled.values()) == len(tables) == 7581
    print('Fully dependent orbits:', representatives)
    print('Paid-gate histogram (size, labelled functions):', sorted(labelled.items()))


if __name__ == '__main__':
    if not __debug__:
        sys.exit('Run without -O to retain verification assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('executable', type=Path)
    parser.add_argument('--cross-check', action='store_true',
                        help='also replay each signed lower bound with the Python verifier')
    args = parser.parse_args()
    main(args.executable.resolve(), args.cross_check)
