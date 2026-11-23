"""Independent exact synthesis using separation of positive-negative pairs."""
from functools import cache
from itertools import combinations
from sys import argv

edges = [(0, 1), (0, 2), (2, 1), (0, 3), (3, 4), (4, 5), (5, 6), (6, 1)]
inputs = [sum(1 << x for x in range(128) if (x >> i) & 1) for i in range(7)]
truth = sum(1 << x for x in range(128) if any((x >> a) & (x >> b) & 1 for a, b in edges))
ones = (1 << 128) - 1
positive = [x for x in range(128) if (truth >> x) & 1]
negative = [x for x in range(128) if not (truth >> x) & 1]
all_pairs = (1 << (len(negative) * len(positive))) - 1


@cache
def distinguishes(wire):
    """Bit (i * len(negative) + j) is set if the wire separates the pair."""
    negative_values = sum(1 << j for j, x in enumerate(negative) if (wire >> x) & 1)
    mask = (1 << len(negative)) - 1
    return sum((negative_values ^ (mask if (wire >> x) & 1 else 0)) << (i * len(negative))
               for i, x in enumerate(positive))


path = {}


@cache
def search(wires, budget):
    if truth in wires:
        return True
    if len(wires) > budget + 1 or not budget:
        return False
    for size in (2, 1):
        for chosen in combinations(wires, size):
            rest = tuple(w for w in wires if w not in chosen)
            a = chosen[0]
            options = [('not', ones ^ a)] if size == 1 else [('and', a & chosen[1]), ('or', a | chosen[1])]
            base = 0
            for w in rest:
                base |= distinguishes(w)
            for op, value in options:
                if value in wires or value in (0, ones):
                    continue
                # The child has len(rest) + k + 1 live wires and budget - 1 gates.
                for k in range(min(size, budget - len(rest) - 1) + 1):
                    for saved in combinations(chosen, k):
                        covered = base | distinguishes(value)
                        for w in saved:
                            covered |= distinguishes(w)
                        if covered != all_pairs:
                            continue
                        child = tuple(sorted((*rest, value, *saved)))
                        if search(child, budget - 1):
                            path[wires, budget] = op, chosen, value, child
                            return True
    return False


if __name__ == '__main__':
    budget = int(argv[1])
    state = tuple(sorted(inputs))
    result = search(state, budget)
    print('SAT' if result else 'UNSAT', budget, 'distinct states', search.cache_info().misses)
    if result:
        wires = list(inputs)
        while truth not in state:
            op, chosen, value, state = path[state, budget]
            print(op, *[wires.index(w) for w in chosen])
            wires.append(value)
            budget -= 1
        print('output', wires.index(truth))
