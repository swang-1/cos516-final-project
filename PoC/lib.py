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
    def __init__(self, rel, arg_sorts, prime=None, neg=False, unique_args=False):
        self.relation = rel
        self.prime = prime
        self.arg_sorts = arg_sorts
        self.neg = neg
        self.unique_args = unique_args

    def _validate_args(self, args):
        assert len(args) == len(self.arg_sorts), f"Incorect number of arguments. Expected {len(self.arg_sorts)} but got {len(args)}"
        for i in range(len(args)):
            if args[i].sort() != self.arg_sorts[i]:
                raise AssertionError(f"Incorrect sort of argument at position {i}. \
                                     Expected {self.arg_sorts[i]} but got {args[i].sort()}")

    def negate(self):
        return Relation(self.relation, self.arg_sorts, self.prime, (not self.neg), self.unique_args)

    def instantiate(self, args, primed=False):
        self._validate_args(args)
        if primed:
            if self.prime is not None:
                app = self.prime(*args)
            else:
                raise AssertionError(f"Tried applying to prime function that doesn't exist")
        else:
            app = self.relation(*args)

        return z3.Not(app) if self.neg else app
    
class App():
    def __init__(self, rel, args):
        self.relation = rel
        self.args = args

    def instantiate(self, primed=False):
        return self.relation.instantiate(self.args, primed)

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
    
    return Relation(e, (sort, sort), unique_args=True)

class Invariant():
    def __init__(self, lhs=Conj([]), rhs=Disj([]), qvars=[]):
        self.lhs = lhs
        self.rhs = rhs
        self.qvars = qvars
    
    def formula(self):
        return z3.ForAll(self.qvars, z3.Implies(self.lhs.formula(), self.rhs.formula()))