# Verified SAT Solver in Coq

A brute-force Boolean satisfiability (SAT) solver written in Coq, with machine-checked proofs of its soundness, plus a verified formula optimizer and a verified negation normal form (NNF) converter.

- **Source:** [plf/SatSolver.v](plf/SatSolver.v)
- **Report:** [Report.pdf](Report.pdf)
- **Assignment:** [Project description.md](Project%20description.md)

The `lf/` and `plf/` directories hold the *Software Foundations* volumes (*Logical Foundations* and *Programming Language Foundations*) used during the course. `SatSolver.v` is self-contained and depends only on the Coq standard library.

## Building

Requires Coq (tested with Coq/Rocq 9.x; earlier 8.x versions should also work).

```sh
cd plf
coqc SatSolver.v
```

If compilation succeeds, every proof has been checked. Coq 9 prints `"From Coq" has been replaced by "From Stdlib"` deprecation warnings, which you can ignore.

## What's inside

### Formulas and semantics

```coq
Inductive form :=
  | FVar  : string -> form
  | FTrue | FFalse
  | FAnd  : form -> form -> form
  | FOr   : form -> form -> form
  | FImp  : form -> form -> form
  | FNot  : form -> form.
```

A custom notation lets you write formulas directly, e.g. `<{ (x \/ ~y) /\ (~x \/ y) }>`.

| Definition | Kind | Meaning |
|---|---|---|
| `valid V p` | `Prop` | `p` holds under valuation `V` (truth-table semantics) |
| `satisfiable p` | `Prop` | `exists V, valid V p` |
| `eval_form V p` | `bool` | Computable evaluation of `p` under `V` |

### Solver

`find_valuation` works in three steps:

1. Collect the distinct variables of `p` (`find_vars`).
2. Generate all 2ⁿ Boolean assignments (`gen_bool_perms`) and turn each into a valuation (`gen_valuations`).
3. Return the first valuation that makes `eval_form` true, or `None` if there isn't one.

`solver p` returns `true` exactly when `find_valuation p` finds a valuation.

### Main results

| Theorem | Statement |
|---|---|
| `eval_form_valid` | `eval_form V p = true <-> valid V p` |
| `solver_sound` | `solver p = true -> satisfiable p` |
| `optimizer_eval_form` | `eval_form V p = eval_form V (optimizer p)` |
| `optimizer_satisfiable` | `satisfiable p <-> satisfiable (optimizer p)` |
| `nnf_converter_eval_form` | `eval_form V p = eval_form V (nnf_converter p)` |
| `nnf_solver_sound` | `nnf_solver p = true -> satisfiable p` |

### Extensions implemented

- **Extension 1 (optimizer):** `optimizer` simplifies `∧`/`∨` with `⊤`/`⊥` using the identity and absorption laws. It is proved to preserve evaluation, validity and satisfiability.
- **Extension 2 (NNF):** `nnf_converter` and `nnf_negator` are mutually recursive and push negations down to the variables, also rewriting `p → q` as `¬p ∨ q`. `nnf_solver` runs the solver on the converted formula and is proved sound.

### Tests

The file includes `Example`s checked by `reflexivity`. They cover variable extraction, permutation generation, evaluation, and positive and negative solver cases such as `x ∨ ¬x` (satisfiable) and `¬x ∧ x` (unsatisfiable).

## Limitations

- Exponential time: the solver enumerates all 2ⁿ assignments.
- Soundness only. Completeness (`satisfiable p -> solver p = true`) is not proved.
