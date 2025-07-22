import itertools

def H(Set, n):
    combinations = list(itertools.combinations(Set, 3))
    for i in range (len(combinations)):
        a, b, c = combinations[i]
        if (a + b + c) % n == 0:
            return False, [a, b, c], combinations
    return True, combinations