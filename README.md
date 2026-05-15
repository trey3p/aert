# aert - automated explicit refinement types
See examples of the language in action inside the `tests` folder!

## Project Structure
The following files are in the `Ambifine` folder.
- `Surface.lean` defines the surface syntax for the language
- `Elab.lean` elaborates the surface syntax
- `Infer.lean` and `Check.lean` are used to typecheck the language
- `UntypedToExpr.lean` implements the translation from the language to Lean
- `Tactics.lean` implements the `decidable_reduce` tactic

## Advantages of explicity refinement types with automation
There are advantages to having explicit refinement types with automation:
 * Allows user input and help to get to decidable theories.
 * Eliminates solvers and other algorithms from the trusted code base.
 * When used with solvers that produce proofs, explicit refinement types eliminate expensive runtime checks by running automation once and storing the generated proof for later.
 * Enables reuse of previous theorems and allows proofs by induction.
