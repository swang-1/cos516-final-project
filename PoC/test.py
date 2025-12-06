import z3
import Examples.Ring as Ring
import Examples.DecentralizedLock as Lock
import Examples.TwoPhaseCommit as Commit
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
    res = InvariantSearch.generate_invariants(Ring.qvars, Ring.relations, 1)
    # for inv in res:
    #     print(f"Invariant: {inv.formula()}")
    print(len(res))

def test_generate_invariants_depth2():
    res = InvariantSearch.generate_invariants(Lock.qvars, Lock.relations, 2)
    print(len(res))

def test_generate_invariants_with_arity_0():
    qvars = Commit.qvars
    relations = Commit.relations
    res = InvariantSearch.generate_invariants(qvars, relations, 1, 2)
    print(len(res))


def test_ring_transitions():
    # Invariant: pending S D ∧ btw S N D → le N S
    # This should be inductive on its own
    b1 = lib.App(Ring.pending_rel, [Ring.x, Ring.z])
    b2 = lib.App(Ring.btw_rel, [Ring.x, Ring.y, Ring.z])
    b3 = lib.App(Ring.le_rel, [Ring.y, Ring.x])
    inv = lib.Invariant(lib.Conj([b1, b2]), lib.Disj([b3]))

    print("testing send")
    s = z3.Solver()
    s.add(Ring.axioms)
    s.add(Ring.send)
    s.add(inv.formula())
    s.add(z3.Not(inv.formula(primed=True)))
    assert s.check() == z3.unsat, f"Expected solver to return unsat but got {s.check()}"
    print("send passed: send preserves invariant")

    print("testing recv")
    r = z3.Solver()
    r.add(Ring.axioms)
    r.add(Ring.recv)
    r.add(inv.formula())
    r.add(z3.Not(inv.formula(primed=True)))
    assert r.check() == z3.unsat, f"Expected solver to return unsat but got {r.check()}"
    print("recv passed: recv preserves invariant")

def test_invariant_search_for_ring():
    # pending L L → le N L
    a1 = lib.App(Ring.pending_rel, [Ring.x, Ring.x])
    a2 = lib.App(Ring.le_rel, [Ring.y, Ring.x])
    inv1 = lib.Invariant(lib.Conj([a1]), lib.Disj([a2]))

    # pending S D ∧ btw S N D → le N S
    b1 = lib.App(Ring.pending_rel, [Ring.x, Ring.z])
    b2 = lib.App(Ring.btw_rel, [Ring.x, Ring.y, Ring.z])
    b3 = lib.App(Ring.le_rel, [Ring.y, Ring.x])
    inv2 = lib.Invariant(lib.Conj([b1, b2]), lib.Disj([b3]))
    cands = [inv1, inv2]

    res, success = InvariantSearch.invariant_search(Ring.axioms, Ring.init, Ring.trs, cands, Ring.cex1, debug=True)
    assert success, "Expected invariant search to succeed but failed"
    for inv in res:
        print(inv.formula())


if __name__ == "__main__":
    # Uncomment tests to run

    # test_app_and_relation()
    # test_generate_invariants_depth1()
    # test_generate_invariants_depth2()
    # test_generate_invariants_with_arity_0()

    # test_combos_up_to_len_depth1()
    # test_combos_up_to_len_depth2()

    # test_get_clause_instantiations1()
    # test_get_clause_instantiations2()

    # test_ring_transitions()
    # test_invariant_search_for_ring()
    
    pass