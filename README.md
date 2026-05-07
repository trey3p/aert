# aert - automated explicit refinement types
There are advantages to having explicit refinement types with automation:
 * Allows user input and help to get to decidable theories.
 * Eliminates solvers and other algorithms (like liquid typing) from the trusted code base.
 * When used with solvers that produce proofs, explicit refinement types eliminate expensive runtime checks by running automation once and storing the generated proof for later.
* Some properties require quantifiers to be stated naturally. aert allows you to state these properties naturally and then use automation and proving to prove them. Tools like Liquid Haskell typically require users to state properties in a restricted fragment of FOL.
* Enables reuse of previous theorems and allows proofs by induction.

## Theories that aer can handle
  * Reducing to EPR Class : given a formula ∀ ∃ ∀ the user can provide existential witnesses to get the theory within EPR (∃ ∀ ).
  * Presburger + Nonlinear Arithmetic: Given a formula in Nonlinear arithmetic, the user can provide explicit proofs that reduce the formula to presburger arithmetic at which point automation can discharge the rest of the goal.

Example for Presburger:

vector is an example


Example for Nonlinear Arithmetic:

```
flatIndex : (rows : {r : Nat | r > 0}) 
          → (cols : {c : Nat | c > 0})
          → (i : {x : Nat | x < rows}) 
          → (j : {x : Nat | x < cols})
          → {k : Nat | k < rows * cols}
flatIndex rows cols i j = i * cols + j
```

```flatIndex``` takes converts an index ```(i, j)``` for a 2D array of size ```row x cols``` into an index ```k``` for a flat array that stores the 2D grid in row-major order. The refinement on ```k``` ensures that ```k``` is within bounds.

The typechecker cannot solve this on its own since it requires verifying:
``` rows > 0 ∧ cols > 0 ∧ i < rows ∧ j < cols ⇒ i * cols + j < rows * cols```
We cannot call out to a solver for this since this formula sits in nonlinear arithmetic.

However, given a proof of:
``` rows > 0 ∧ cols > 0 ∧ i < rows ∧ j < cols ⇒ i * cols ≤ rows * cols - cols ```

Let ``` a = i * cols ``` and ```b = row * cols```.
The condition the typechecker needs to solve is
```a + j < b```
given 
```
rows > 0 ∧ cols > 0 ∧ i < rows ∧ j < cols
a ≤ b - cols
```
.

The user provided a lemma that related ```i * cols``` and ```row * cols``` and then abstracted these out, giving a new equisatisfiable formula in Presburger.

The general recipe is something like:


1. Identify the nonlinear subterms
2. Ask the user to prove linear relationships between them
3. Abstract the nonlinear subterms into fresh variables
4. Hand the linear relationships plus the abstracted goal to omega

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
