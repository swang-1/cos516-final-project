import z3
import Examples.Ring as Ring
import InvariantSearch
import lib

def test_app_and_relation():
    x = Ring.x
    leader = Ring.leader_rel

    app = lib.App(leader, [x])
    print(f"instantiation: {app.instantiate()}")

def test_combos_up_to_len_depth1():
    print("Testing `combos_up_to_len` for max_depth = 1")
    out = InvariantSearch.combos_up_to_len(["even", "eq"], 1)
    for combo in out:
        print(combo)

def test_combos_up_to_len_depth2():
    print("Testing `combos_up_to_len` for max_depth = 2")
    out = InvariantSearch.combos_up_to_len(["even", "eq"], 2)
    for combo in out:
        print(combo)

def test_get_clause_instantiations1():
    print("Testing get_clause_instantiations")
    A = z3.DeclareSort('A')
    B = z3.DeclareSort('B')

    a1 = z3.Const('a1', A)
    a2 = z3.Const('a2', A)
    b1 = z3.Const('b1', B)
    b2 = z3.Const('b2', B)

    r1 = z3.Function('r1', A, B, z3.BoolSort())
    r2 = z3.Function('r2', A, B, z3.BoolSort())

    rel1 = lib.Relation(r1, [A, B])
    rel2 = lib.Relation(r2, [A, B])

    qvars_by_sort = {
        A: [a1, a2],
        B: [b1, b2]
    }

    out = InvariantSearch.get_clause_instantiations(qvars_by_sort, [rel1, rel2])
    for inst in out:
        print([app.instantiate() for app in inst])

def test_get_clause_instantiations2():
    print("Testing get_clause_instantiations")
    A = z3.DeclareSort('A')

    a1 = z3.Const('a1', A)
    a2 = z3.Const('a2', A)

    r1 = z3.Function('r1', A, A, z3.BoolSort())
    r2 = z3.Function('r2', A, A, z3.BoolSort())

    rel1 = lib.Relation(r1, [A, A])
    rel2 = lib.Relation(r2, [A, A])

    qvars_by_sort = {
        A: [a1, a2]
    }

    out = InvariantSearch.get_clause_instantiations(qvars_by_sort, [rel1, rel2])
    for inst in out:
        print([app.instantiate() for app in inst])

def test_generate_invariants_depth1():
    res = InvariantSearch.generate_invariants(Ring.qvars, Ring.sorts, Ring.relations, 1)
    for lhs, rhs in res:
        print(f"lhs:{[app.instantiate() for app in lhs]}, rhs: {[app.instantiate() for app in rhs]}")

if __name__ == "__main__":
    # test_app_and_relation()
    test_generate_invariants_depth1()

    # test_combos_up_to_len_depth1()
    # test_combos_up_to_len_depth2()

    # test_get_clause_instantiations1()
    # test_get_clause_instantiations2()