"""Emit one concrete Lean upper-bound theorem per circuit in optima.txt."""
from argparse import ArgumentParser
from pathlib import Path


def main(path):
    rows = [line.split() for line in path.read_text().splitlines()
            if line and len(line.split()[0]) == 8 and all(c in '0123456789abcdef' for c in line.split()[0])]
    assert len(rows) == len({t for t, *_ in rows}) == 95
    print('''import PEqualNP.Defs.CircuitLowerBounds

namespace FiveInputUpper
open PEqualNP.CircuitLowerBounds

def Upper (table budget : Nat) : Prop :=
  ∃ C : Circuit, C.gates.length = budget ∧
    (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
    ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) =
      table.testBit (∑ i : Fin 5, if x i then 2 ^ (i : Nat) else 0)
''')
    for table, _, size_text, *description in rows:
        size = int(size_text)
        assert size == len(description)
        gates = []
        for j, entry in enumerate(description):
            op, a, b = entry.split(',')
            assert 0 <= int(a) < int(b) < 5 + j
            name = {'A': 'and', 'O': 'or'}[op]
            gates.append(f'⟨.{name}, [{a}, {b}]⟩')
        print(f'private def gs_{table} : List Gate := [{", ".join(gates)}]')
        print(f'theorem upper_{table} : Upper 0x{table} {size} := by')
        print(f'  refine ⟨⟨gs_{table}, {4 + size}⟩, rfl, ?_, ?_⟩')
        print(f'  · simp [gs_{table}]')
        print('  · decide +kernel\n')
    print('end FiveInputUpper')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('optima', type=Path)
    main(parser.parse_args().optima)
