# The Estates - A Constraint Programming Project in MiniZinc

## What is this about?

Imagine you have a piece of land (a board) and you need to place **estates of different shapes** (like Tetris pieces, but more complex) without overlapping, respecting paths, parks, and some neighborhood rules. Now imagine that instead of telling the computer *how* to place the pieces step by step, you simply tell it *what rules* a valid solution must satisfy. Welcome to the world of **Constraint Programming**!

This project is a practical assignment for the course *Declarative Programming* where we explore this different paradigm using **MiniZinc**, a language specifically designed for solving **CSP ** (Constraint Satisfaction Problems).

## The problem in a nutshell

We have:
- A board of variable size
- Parks and paths (forbidden cells for construction)
- A set of estates with specific shapes (each with an ID from 1 to 13)
- Incompatibility rules (some estates cannot touch each other)
- Some estates *need* to be adjacent to a park

The goal: **place ALL estates on the board respecting all the rules** (or determine that it is impossible).

## Why is it interesting?

Because it makes you think backwards:
- You don't program *how* to solve the problem
- You program *what* constitutes a valid solution
- The solver (Gecode, Chuffed, etc.) takes care of finding the solution (or telling you none exists)

It's like giving a gifted friend the instructions to a board game and letting them figure out how to win on their own.

## What we learned

- **Viewpoints**: There are many ways to model the same problem. We explored two:
  - **Viewpoint 1**: The estate as an object (position + orientation)
  - **Viewpoint 2**: Each cell of each estate as an independent variable
  
- **Heuristics MATTER**: `first_fail` is not the same as `input_order`. Depending on the solver and the problem, one can be 500 times faster than the other.

- **Chuffed vs Gecode**: The former learns from its mistakes (clauses), the latter is more brute-force but sometimes more predictable.

## How to try it

1. Install MiniZinc from [minizinc.org](https://www.minizinc.org)
2. Open any of the `.mzn` files
3. Choose an instance (we have from d1 to d10)
4. Run it!

```bash
minizinc --solver chuffed viewpoint1.mzn instance_d1.dzn
```
## The instances
We created 10 problems of increasing difficulty:

- Easy (d1-d3): Few estates, generous board

- Medium (d4-d6): Incompatibilities and requirements start to appear

- Hard (d7-d10): Some are unsatisfiable (UNSAT), others have very tight combinations

## Final thoughts
Programming with constraints is an experience that every programmer should try at least once. It forces you to abstract away from algorithms and think in terms of relationships and properties. And when the solver finds a solution in milliseconds to a problem that would have taken you hours to program... the feeling is incredible!