# Search for witnesses of the two k=2 pairs of V6 Section 7.1.
# tau(x,y) = (f(f(x,y), f(x,x)), f(x,x))
# sigma(x,y) = (f(x,y), f(f(x,x), f(y,y)))
import itertools, sys, random

def tau_map(f, n):
    out = []
    for x in range(n):
        for y in range(n):
            d = f[x][x]
            out.append((f[f[x][y]][d], d))
    return out

def sigma_map(f, n):
    out = []
    for x in range(n):
        for y in range(n):
            out.append((f[x][y], f[f[x][x]][f[y][y]]))
    return out

def is_bij(out):
    return len(set(out)) == len(out)

def brute(n, mapf):
    cells = [(x, y) for x in range(n) for y in range(n)]
    for vals in itertools.product(range(n), repeat=n*n):
        f = [[vals[x*n+y] for y in range(n)] for x in range(n)]
        if is_bij(mapf(f, n)):
            return f
    return None

# n = 2 exhaustive for both
for name, mf in (("tau", tau_map), ("sigma", sigma_map)):
    print(name, "n=2 witness:", brute(2, mf))
print("tau n=3 witness:", brute(3, tau_map))
print("sigma n=3 witness:", brute(3, sigma_map))
sys.stdout.flush()

# sigma n = 4: backtracking search. Order cells so that constraints propagate.
def sigma_backtrack(n, seed=0, limit=2_000_000):
    rng = random.Random(seed)
    f = [[None]*n for _ in range(n)]
    # assign diagonal first (d(x) = f(x,x)), then the rest
    cells = [(x, x) for x in range(n)] + [(x, y) for x in range(n) for y in range(n) if x != y]
    nodes = [0]
    def outputs_partial():
        # returns list of defined outputs or None if conflict
        seen = set()
        for x in range(n):
            for y in range(n):
                a = f[x][y]
                if a is None: continue
                dx, dy = f[x][x], f[y][y]
                if dx is None or dy is None: continue
                b = f[dx][dy]
                if b is None: continue
                if (a, b) in seen: return False
                seen.add((a, b))
        return True
    def rec(i):
        nodes[0] += 1
        if nodes[0] > limit: return None
        if i == len(cells):
            return [row[:] for row in f]
        x, y = cells[i]
        order = list(range(n)); rng.shuffle(order)
        for v in order:
            f[x][y] = v
            if outputs_partial():
                r = rec(i+1)
                if r is not None: return r
            f[x][y] = None
        return None
    return rec(0)

for seed in range(5):
    w = sigma_backtrack(4, seed)
    print("sigma n=4 seed", seed, "witness:", w)
    if w is not None:
        print("check:", is_bij(sigma_map(w, 4)))
        break
