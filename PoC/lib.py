import z3

class Spec():
    _sorts = []
    _relations = []
    
    def __init__(self, sorts=[], relations = []):
        self._sorts = sorts
        self._relations = relations


class Conj():
    def __init__(self, conj=[]):
        self.conj = conj

    def formula(self):
        if len(self.conj) > 0:
            return z3.And(self.conj)
        else:
            return z3.BoolVal(True)


class Disj():
    def __init__(self, disj=[]):
        self.disj = disj

    def formula(self):
        if len(self.disj) > 0:
            return z3.Or(self.disj)
        else:
            return z3.BoolVal(False)

class Relation():
    def __init__(self, rel, arity, arg_sorts, prime=None):
        self.relation = rel
        self.prime = prime
        self.arity = arity
        self.arg_sorts = arg_sorts

    def _validate_args(self, args):
        assert len(args) == self.arity, f"Incorect number of arguments. Expected {self.arity} but got {len(args)}"
        for i in range(len(args)):
            if args[i].sort() != self.arg_sorts[i]:
                raise AssertionError(f"Incorrect sort of argument at position {i}. \
                                     Expected {self.arg_sorts[i]} but got {args[i].sort()}")

    def instantiate(self, args, primed=False, neg=False):
        self._validate_args(args)
        if primed:
            if self.prime is not None:
                app = self.prime(*args)
            else:
                raise AssertionError(f"Tried applying to prime function that doesn't exist")
        else:
            app = self.relation(*args)

        return z3.Not(app) if neg else app
    
class App():
    def __init__(self, rel, args, neg=False):
        self.relation = rel
        self.args = args
        self.neg = neg

    def instantiate(self, primed=False):
        return self.relation.instantiate(self.args, primed, self.neg)

def eq_rel(sort):
    '''
    A utility function that returns a Relation object representing
    the equality relation over the given sort.

    input:
        sort: A Z3 Sort object
    output:
        A relation object r, where:
            r.relation(x, y) := x == y
            r.arity = 2
            r.arg_sorts = (sort, sort)
    '''
    def e(x, y):
        assert z3.is_eq(x == y), "expression {x} == {y} is not a z3 equality expression"
        return x == y
    
    return Relation(e, 2, (sort, sort))

class Invariant():
    def __init__(self, lhs=Conj([]), rhs=Disj([]), qvars=[]):
        self.lhs = lhs
        self.rhs = rhs
        self.qvars = qvars
    
    def formula(self):
        return z3.ForAll(self.qvars, z3.Implies(self.lhs.formula(), self.rhs.formula()))