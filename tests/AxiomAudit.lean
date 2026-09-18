import Submission
import Lean

example : Kriterion.Solution := Submission.solution

run_cmd do
  let illegal := (← Lean.collectAxioms `Submission.solution).filter fun name =>
    !#[`propext, `Classical.choice, `Quot.sound].contains name
  unless illegal.isEmpty do
    Lean.throwError m!"The baseline uses disallowed axioms: {illegal}"
