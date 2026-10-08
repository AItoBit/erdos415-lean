"""Exact finite evidence; this script is not a Lean proof."""
from math import factorial

N = 826
phi = list(range(N + 1))
for p in range(2, N + 1):
    if phi[p] == p:
        for a in range(p, N + 1, p):
            phi[a] -= phi[a] // p


def pattern(values):
    if len(set(values)) != len(values):
        return None
    ranks = {v: i + 1 for i, v in enumerate(sorted(values))}
    return tuple(ranks[v] for v in values)


def witnesses(k):
    found = {}
    for m in range(N - k + 1):
        values = tuple(phi[m + 1:m + k + 1])
        pi = pattern(values)
        if pi is not None:
            found.setdefault(pi, (m, values))
    return found


for k in (3, 4):
    found = witnesses(k)
    print(f"k={k}: {len(found)} of {factorial(k)} patterns")
    for pi, (m, values) in sorted(found.items()):
        print("".join(map(str, pi)), "m=", m, "values=", values)

assert len(witnesses(3)) == 6
assert len(witnesses(4)) == 15
assert (1, 2, 3, 4) not in witnesses(4)
assert (4, 3, 2, 1) in witnesses(4)
assert tuple(phi[823:827]) == (822, 408, 400, 348)
