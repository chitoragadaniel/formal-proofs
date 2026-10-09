# SAT Solver

The code for the project lies in [plf/SatSolver.v](plf/SatSolver.v)

Report of the project is available [here](report.pdf). 

## Description

The goal of this project is to implement a Boolean Satisfiability (SAT) solver in Coq and to prove the soundness of your implementation.

Boolean formulas are given by the following grammar:

```
p, q ::= x | ⊤ | ⊥ | p ∧ q | p ∨ q | p → q | ¬p
```

Here, `x` ranges over an infinite set of propositional variables. Examples of formulas are:

- `(x ∨ ¬y) ∧ (¬x ∨ y)`
- `¬y → (x ∨ y)`
- `x ∧ ¬x ∧ ⊤`

A Boolean formula `p` is said to be *satisfiable* in case its truth table contains at least one row whose outcome is 1. For example, the formula `¬y → (x ∨ y)` has the truth table

| x | y | ¬y → (x ∨ y) |
|---|---|--------------|
| f | f | f |
| t | f | t |
| f | t | t |
| t | t | t |

and thus is satisfiable. The formula `x ∧ ¬x ∧ ⊤` has the truth table

| x | x ∧ ¬x ∧ ⊤ |
|---|------------|
| f | f |
| t | f |

and hence is not satisfiable.

## Exercises

Complete all the exercises below.

The first part of this project is to represent Boolean formulas in Coq and to formally define the notion of satisfiability.

### Exercise 1

```coq
Inductive form :=
| FVar : string -> form
(* fill in *) .
```

### Exercise 2

Give Coq definitions of type `form` corresponding to:

- `(x ∨ ¬y) ∧ (¬x ∨ y)`
- `¬y → (x ∨ y)`
- `x ∧ ¬x ∧ ⊤`

In order to define satisfiability we introduce the notion of a *valuation*, which is a function that assigns true or false to each propositional variable.

```coq
Definition valuation := string -> bool.
```

### Exercise 3

Define validity of Boolean formulas (using the "truth table semantics") via a recursive `Prop`-valued function:

```coq
Fixpoint valid (V : valuation) (p : form) : Prop :=
(* fill in *) .
```

A formula is said to be satisfiable if there exists a valuation that makes the formula true. This corresponds to the following definition in Coq:

```coq
Definition satisfiable (p : form) : Prop :=
  exists V : valuation, valid V p.
```

### Exercise 4

Prove in Coq that `(x ∨ ¬y) ∧ (¬x ∨ y)` and `¬y → (x ∨ y)` are satisfiable. You should create two lemmas of the shape below, replacing *formula X* with the respective formulas in the lemma:

```coq
Lemma testX : satisfiable (* formula X *) .
```

### Exercise 5

Define a function `find_valuation` that, given a formula `p`, computes a valuation in which `p` is true. You should implement this function by enumerating all possible valuations, i.e., you should generate the formula's truth table and check if there is a row whose outcome is 1. The function `find_valuation` should yield `None` in case no such valuation exists.

```coq
Definition find_valuation (p : form) : option valuation :=
(* fill in *) .
```

We now define our SAT solver as follows:

```coq
Definition solver (p : form) : bool :=
  match find_valuation p with
  | Some _ => true
  | None   => false
  end.
```

### Exercise 6

Explain the difference between `satisfiable` and `solver`.

### Exercise 7

Write 2 positive and 2 negative tests of the solver and prove these through proof by simplification via the `reflexivity` tactic.

### Exercise 8

Prove that `solver` is sound. That means:

```coq
Theorem solver_sound p :
  solver p = true -> satisfiable p.
```

You might want to state a helper lemma first, which you should prove by varying the induction hypothesis.

### Exercise 9

Implement one of the extensions below.

## Extensions

Choose one of the extensions below.

### Extension 1 (easy)

Write an optimizer that simplifies a Boolean formula using the laws below, and prove correctness of your optimizer.

- `x ∧ ⊤ = x`
- `⊤ ∧ x = x`
- `x ∧ ⊥ = ⊥`
- `⊥ ∧ x = ⊥`
- `x ∨ ⊤ = ⊤`
- `⊤ ∨ x = ⊤`
- `x ∨ ⊥ = x`
- `⊥ ∨ x = x`

### Extension 2 (moderate)

Write a converter that transforms Boolean formulas into negation normal form and formulate and prove correctness of your converter. A Boolean formula is in *negation normal form* if the negation operator `¬` is only applied to variables. You should incorporate your converter into the solver and its correctness proof, that is, prove `nnf_solver p = true -> satisfiable p` for an adequately defined `nnf_solver`.

### Extension 3 (difficult)

Prove completeness of your solver. That means:

```coq
Lemma solver_complete p :
  satisfiable p -> solver p = true.
```

### Extension 4 (very difficult)

Implement a more efficient SAT solver, like one based on the Davis-Putnam-Logemann-Loveland (DPLL) algorithm, and prove its correctness (that is, soundness).

