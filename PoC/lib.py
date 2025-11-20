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


class Invariant():
    def __init__(self, lhs=Conj([]), rhs=Disj([])):
        self.lhs = lhs
        self.rhs = rhs
    
    def formula(self):
        return z3.Implies(self.lhs.formula(), self.rhs.formula())