def subset(s, n):
    if n > len(s) or n < 0:
        return []
    elif n == len(s):
        return [s]
    elif n == 0:
        return [[]]
    else:
        return subset(s[1:], n) + [[s[0]] + sub for sub in subset(s[1:], n - 1)]

class MultiSet(set):
    
    def __init__(self, *args):
        assert len(args) <= 1
        self.cardinal = dict()
        if len(args) == 1:
            if type(args[0]) == MultiSet:
                self.cardinal = dict(args[0].cardinal)
            elif type(args[0]) == set:
                for element in list(args[0]):
                    self.cardinal[element] = 1
            else:
                for element in args[0]:
                    if element not in self.cardinal:
                        self.cardinal[element] = 1
                    else:
                        self.cardinal[element] += 1
        
    def __repr__(self):
        return f'MultiSet({repr(self.cardinal)[1:-1]})'

    def __iter__(self):
        def f():
            if self.cardinal != dict():
                elem = list(self.cardinal.keys())[0]
                for i in range(list(self.cardinal.values())[0]):
                    yield elem
                yield from iter(MultiSet(self).delete(elem))
        return f()

    def __contains__(self, arg):
        return arg in self.cardinal

    def __eq__(self, arg):
        return self.cardinal == arg.cardinal

    def __get__(self, index):
        return list(self.cardinal.keys())[index]

    def add(self, element, number = 1):
        assert number > 0
        if element in self.cardinal:
            self.cardinal[element] += number
        else:
            self.cardinal[element] = number
        return self

    def remove(self, element, number = 1):
        assert number > 0
        if element in self.cardinal:
            if self.cardinal[element] > number:
                self.cardinal[element] -= number
            else:
                self.cardinal.pop(element)
        return self

    def delete(self, element):
        self.cardinal.pop(element)
        return self

    def count(self, element):
        if element in self.cardinal:
            return self.cardinal[element]
        else:
            return 0

    def union(self, *args):
        if len(args) == 0:
            return self
        if len(args) == 1:
            s, arg = MultiSet(self), args[0]
            if type(arg) == set:
                for element in list(arg):
                    if element not in s:
                        s.add(element)
            elif type(arg) == MultiSet:
                for element in arg:
                    if element not in s:
                        s.add(element, arg.count(element))
                    else:
                        s.cardinal[element] = max(s.count(element), arg.count(element))
            return s
        else:
            return self.union(args[0]).union(*args[1:])

    def intersection(self, *args):
        if len(args) == 0:
            return self
        if len(args) == 1:
            s, arg = MultiSet(), args[0]
            if type(arg) == set:
                for element in list(arg):
                    if element in self:
                        s.cardinal[element] = 1
            elif type(arg) == MultiSet:
                for element in arg:
                    if element in self:
                        s.cardinal[element] = min(self.count(element), arg.count(element))
            return s
        else:
            return self.intersection(args[0]).intersection(*args[1:])

    def exclusion(self, arg):
        assert type(arg) == MultiSet
        s = MultiSet(self)
        for i in range(len(arg.cardinal.keys())):
            s.remove(list(arg.cardinal.keys())[i], list(arg.cardinal.values())[i])
        return s

    def size(self):
        return sum(self.cardinal.values())

    def subset(self, n):
        assert n >= 0
        if n == 0:
            return [MultiSet()]
        elif self.cardinal == dict():
            return []
        else:
            possible = []
            for i in range(min(n, list(self.cardinal.values())[0]) + 1):
                s = MultiSet(self)
                s.delete(list(self.cardinal.keys())[0])
                possible += [MultiSet([list(self.cardinal.keys())[0]] * i).union(k) for k in s.subset(n - i)]
            return possible

    def ordered_subset(self, n):
        assert n >= 0
        if n == 0:
            return [[]]
        elif self.cardinal == dict():
            return []
        else:
            possible = []
            for elem in list(self.cardinal.keys()):
                s = MultiSet(self)
                s.remove(elem)
                possible += [[elem] + k for k in s.ordered_subset(n - 1)]
            return possible

    def permute(self):
        if self.cardinal == dict():
            return [[]]
        else:
            possible = []
            for elem in list(self.cardinal.keys()):
                s = MultiSet(self)
                s.remove(elem)
                possible += [[elem] + k for k in s.permute()]
            return possible

def reformat(structure, theorem):
    assert type(structure) == type(theorem) == list
    assert (n := len(structure)) == len(theorem)
    assert all(type(element) == MultiSet for element in structure) and all(type(element) == MultiSet for element in theorem)
    assert all(structure[i].size() == theorem[i].size() for i in range(n))

    def perm(total, k):
        if k == 0:
            return ['0' * total]
        elif k == total:
            return ['1' * total]
        elif total == 0:
            return []
        else:
            return ['0' + p for p in perm(total - 1, k)] + ['1' + p for p in perm(total - 1, k - 1)]
    order = sum([perm(n, i) for i in range(n + 1)], []) 

    def f(st, th, index):
        assert index >= 0
        if index == 0:
            return [dict()]
        else:
            possible = []
            s = order[index]
            stIntersection = MultiSet.intersection(*[st[i] for i in range(n) if int(s[i])])
            thIntersection = MultiSet.intersection(*[th[i] for i in range(n) if int(s[i])])
            if stIntersection.size() < (req := thIntersection.size()):
                return []
            for subset in stIntersection.subset(req):
                stCopy, thCopy = list(map(MultiSet, st)), list(map(MultiSet, th))
                for i in range(n):
                    if int(s[i]):
                        stCopy[i] = stCopy[i].exclusion(subset)
                        thCopy[i] = thCopy[i].exclusion(thIntersection)
                cumulative_dict = f(stCopy, thCopy, index - 1)
                for p in subset.permute():
                    for d in cumulative_dict:
                        dCopy = dict(d)
                        for a, b in zip(thIntersection, p):
                            dCopy[a] = b
                        possible.append(dCopy)
            return possible
    return f(structure, theorem, (1 << n) - 1)
            

